# CLAUDE.md - Developer Guide for Guardrails: Atomic

This document contains all the information needed to understand and contribute to the Guardrails: Atomic project. It's designed to help AI assistants (like Claude) and human developers quickly get up to speed.

---

## Table of Contents

1. [Project Overview](#project-overview)
2. [Core Concepts](#core-concepts)
3. [Architecture](#architecture)
4. [File Structure](#file-structure)
5. [Implementation Guide](#implementation-guide)
6. [Testing Strategy](#testing-strategy)
7. [Common Tasks](#common-tasks)
8. [Important Constraints](#important-constraints)
9. [Resources](#resources)

---

## Project Overview

**Guardrails: Atomic** is an AI-powered code generation assistant that produces distributed system handlers with **formal correctness guarantees** using CEGIS (Counter-Example Guided Inductive Synthesis) with Z3 SMT solver.

### What Problem Does It Solve?

Writing correct distributed systems code is notoriously difficult. Common bugs include:
- Race conditions under message reordering
- Double-spending under duplicate delivery (at-least-once semantics)
- Partial state updates after crashes
- Idempotency violations

Guardrails: Atomic **automatically generates and verifies** TypeScript handlers that are proven correct under specified fault scenarios.

### Technology Stack

- **Frontend/Backend**: Next.js 15 (App Router)
- **Language**: TypeScript (100%)
- **Styling**: Tailwind CSS
- **Package Manager**: pnpm
- **LLM**: OpenRouter GPT-4
- **Formal Verification**: Z3 SMT Solver (z3-solver npm package)
- **Testing**: Vitest
- **Authentication**: Clerk
- **Database**: MongoDB Atlas (user sessions & history)

---

## Core Concepts

### 1. CEGIS (Counter-Example Guided Inductive Synthesis)

CEGIS is an iterative synthesis approach:

1. **Synthesize**: Generate candidate code using LLM
2. **Verify**: Check code against formal specification using Z3 SMT solver
3. **Counterexample**: If bugs found, extract model showing violation
4. **Refine**: Use counterexample to guide LLM to fix the code
5. **Repeat**: Continue until verified or max iterations reached

```
┌─────────────┐
│   Spec      │
│  (YAML)     │
└──────┬──────┘
       │
       ▼
┌─────────────┐     ┌──────────────┐
│     LLM     │────▶│  Generated   │
│  Generate   │     │     Code     │
└─────────────┘     └──────┬───────┘
                            │
                            ▼
                    ┌──────────────┐
                    │  Translate   │
                    │  to Z3       │
                    │  (SMT-LIB)   │
                    └──────┬───────┘
                            │
                            ▼
                    ┌──────────────┐     ┌─────────────┐
                    │      Z3      │────▶│  Verified!  │
                    │   Solver     │ ✓   │   (unsat)   │
                    └──────┬───────┘     └─────────────┘
                            │ ✗
                            │ (sat)
                            ▼
                    ┌──────────────┐
                    │Counterexample│
                    │   (model)    │
                    └──────┬───────┘
                            │
                            ▼
                    ┌──────────────┐
                    │     LLM      │
                    │    Repair    │
                    └──────────────┘
```

### 2. Z3 SMT Solver

Z3 is a Satisfiability Modulo Theories (SMT) solver developed by Microsoft Research. It can check whether logical formulas are satisfiable or prove they are unsatisfiable.

**Key Concepts**:

- **SMT-LIB Format**: Standard input format for Z3 (e.g., `(assert (>= balance 0))`)
- **Sorts**: Types in Z3 (Int, Bool, String, custom types)
- **Constants**: Variables in the problem (e.g., `balance_a1`, `amt`)
- **Assertions**: Constraints that must hold (preconditions, postconditions, invariants)
- **check-sat**: Ask Z3 to check satisfiability
- **get-model**: Extract counterexample when satisfiable

**Result Semantics**:
- **`sat`** = Found a counterexample = **BUG EXISTS** ❌
- **`unsat`** = No counterexample exists = **CODE VERIFIED** ✅
- **`unknown`** = Z3 couldn't decide (timeout/complexity)

**Example SMT-LIB**:
```smt
; Declare variables
(declare-const balance_a1 Int)
(declare-const amt Int)

; Assert preconditions
(assert (>= balance_a1 amt))
(assert (>= amt 0))

; Assert postcondition violation (looking for bugs)
(assert (not (>= (- balance_a1 amt) 0)))

; Check satisfiability
(check-sat)
(get-model)
```

If Z3 returns `unsat`, the postcondition cannot be violated → code is correct!

### 3. Fault Models

The system supports various fault scenarios:

- **Delivery semantics**:
  - `at_least_once`: Messages may be duplicated
  - `exactly_once`: Messages delivered once (ideal, not realistic)
  - `at_most_once`: Messages may be lost
- **Message reordering**: Messages can arrive out of order
- **Crash/restart**: Process can crash and restart, losing in-memory state

### 4. Invariants

Supported invariant types:

- **`idempotent`**: Repeated execution with same request ID has no additional effect
- **`no_double_spend`**: Resources cannot be spent twice (balances stay non-negative)
- **`atomic_no_partial_commit`**: Either all state changes happen or none
- **`conservation`**: Total amount of resources remains constant

---

## Architecture

### Data Flow

#### Natural Language to YAML Spec
```
User Natural Language Input
      ↓
[generate-spec/page.tsx] → Send to API
      ↓
[generate-spec/route.ts] → Call OpenRouter with spec generation prompt
      ↓
[openrouter.service.ts] → LLM generates YAML
      ↓
API Response with YAML Spec
      ↓
[generate-spec/page.tsx] → User can edit YAML in editor
      ↓
User sends final YAML to verification
```

#### CEGIS Loop
```
User YAML Spec
      ↓
[spec-parser.ts] → Parse & Validate with Zod
      ↓
[cegis-loop.ts] → Orchestrate CEGIS iterations
      ↓
┌─────────────────────────────────────┐
│  Iteration Loop (max 8 times)      │
│                                     │
│  1. [code-generator.ts]             │
│     → Call OpenRouter with prompt   │
│     → Get TypeScript code           │
│                                     │
│  2. [z3-generator.ts]               │
│     → Convert spec to Z3 AST        │
│     → Generate SMT-LIB constraints  │
│     → Serialize to SMT-LIB string   │
│                                     │
│  3. [z3-runner.ts]                  │
│     → Initialize z3-solver          │
│     → Load SMT-LIB constraints      │
│     → Run Z3 solver                 │
│     → Parse result (sat/unsat)      │
│                                     │
│  4. If sat (bug found):             │
│     [counterexample-parser.ts]      │
│     → Extract model from Z3         │
│     → Generate feedback             │
│     → Go to step 1 with feedback    │
│                                     │
│  5. If unsat (verified):            │
│     → Return success + proof report │
└─────────────────────────────────────┘
      ↓
API Response to Frontend
```

#### Authentication & Session Management
```
Visitor
      ↓
[app/(auth)/sign-in] → Clerk hosted sign-in UI
      ↓
Clerk session issued → cookie-based JWT
      ↓
[middleware.ts] → Gate protected routes, hydrate user context
      ↓
Server actions/API routes call `auth()` → userId for db operations
```

#### Verification History Persistence
```
Authenticated verification request
      ↓
[lib/history/persistence.ts] → Normalize spec + result payload
      ↓
[lib/db/mongodb.ts] → getMongoClient() singleton (MongoDB Atlas)
      ↓
MongoDB `verification_logs` collection
      ↓
[app/dashboard/history] → Fetch via `/api/history` (paginated)
```

### Directory Structure

```
guardrails-atomic/
├── app/                          # Next.js App Router
│   ├── api/                      # API routes
│   │   ├── verify/               # Main verification endpoint
│   │   ├── validate/             # Spec validation endpoint
│   │   ├── examples/             # Example specs endpoint
│   │   ├── generate-spec/        # NL to YAML endpoint
│   │   ├── history/              # (planned) Fetch saved verification runs
│   │   └── auth/[...clerk]/      # Clerk webhooks & callbacks
│   ├── (auth)/                   # Clerk sign-in/up routes
│   │   ├── sign-in/
│   │   └── sign-up/
│   ├── dashboard/                # Authenticated views
│   │   └── history/              # Saved prompts & results
│   ├── verify/                   # Verification UI page
│   ├── examples/                 # Examples gallery page
│   ├── generate-spec/            # NL to YAML UI page
│   ├── layout.tsx                # Root layout with Nav Bar
│   ├── page.tsx                  # Landing page
│   └── globals.css               # Global styles
│
├── components/                   # React components
│   ├── SpecEditor.tsx            # YAML input
│   ├── CodeViewer.tsx            # Code display
│   ├── ProofReport.tsx           # Verification results
│   ├── IterationHistory.tsx      # CEGIS timeline
│   ├── TraceVisualizer.tsx       # Counterexample display
│   ├── SpecGenerator.tsx         # NL to YAML component
│   └── ui/                       # Base UI components
│
├── lib/                          # Core business logic
│   ├── core/                     # Main CEGIS logic
│   │   ├── cegis-loop.ts         # Orchestration
│   │   ├── spec-parser.ts        # YAML parsing
│   │   └── code-generator.ts     # LLM code gen
│   ├── verification/             # Z3 & verification
│   │   ├── z3-generator.ts       # Spec → Z3 SMT-LIB
│   │   ├── z3-runner.ts          # Z3 execution
│   │   └── counterexample-parser.ts
│   ├── history/                  # Persistence & queries
│   │   └── persistence.ts        # Upsert & fetch helpers
│   ├── db/                       # Database connections
│   │   └── mongodb.ts            # MongoDB Atlas client
│   ├── types/                    # TypeScript types
│   │   ├── specification.ts
│   │   ├── z3-ast.ts
│   │   ├── verification.ts
│   │   └── api.ts
│   ├── services/                 # External services
│   │   └── openrouter.service.ts
│   └── utils/                    # Utilities
│       ├── logger.ts
│       └── errors.ts
│
├── templates/                    # Templates for generation
│   ├── specs/                    # Example YAML specs
│   └── prompts/                  # LLM prompts
│       ├── code-generation.txt
│       ├── code-repair.txt
│       └── spec-generation.txt
│
├── tests/                        # Test suite
│   ├── unit/                     # Unit tests
│   ├── integration/              # Integration tests
│   └── fixtures/                 # Test data
│
├── scripts/                      # Build scripts
│   ├── copy-z3-wasm.ts           # Copy Z3 WASM to public/
│   └── test-z3.ts                # Test Z3 directly
│
├── public/                       # Static assets
│   └── z3/                       # Z3 WASM files
│       ├── z3-built.wasm
│       ├── z3-built.js
│       ├── browser.js
│       └── node.js
│
└── docs/                         # Documentation
    ├── ARCHITECTURE.md           # System design
    └── DEVELOPMENT.md            # Dev guide
```

---

## File Structure

### Critical Files to Understand

#### `lib/types/specification.ts`
Defines the YAML specification schema using Zod. This is the **source of truth** for what specs look like.

Key type: `Specification`
```typescript
{
  name: string;
  signature: { params: Parameter[], returnType: string };
  preconditions: string[];
  postconditions: string[];
  invariants: Invariant[];
  faultModel: FaultModel;
  bounds: Bounds;
}
```

#### `lib/types/verification.ts`
Defines verification results and Z3 output structures.

Key types:
- `VerificationResult` - Final output of CEGIS loop
- `Z3Result` - Result from Z3 solver
- `CounterExample` - Bug trace with suggested fix
- `ProofReport` - Verification success summary

#### `lib/types/z3-ast.ts`
Defines Z3 AST structures for SMT-LIB generation.

Key types:
- `Z3Module` - Top-level Z3 module
- `Z3Constant` - Variable declarations
- `Z3Constraint` - Assertions (preconditions, postconditions, invariants)
- `Z3Assertion` - Individual assert statements

#### `lib/core/cegis-loop.ts`
**Main orchestrator**. Implements the CEGIS loop:
1. Initialize with spec
2. Loop until verified or max iterations:
   - Generate code (with optional feedback)
   - Generate Z3 constraints
   - Run Z3 solver
   - If `sat` (bug found), extract counterexample and loop
   - If `unsat` (verified), return success
3. Return result

#### `lib/core/spec-parser.ts`
Parses YAML spec to typed `Specification` object.
- Use `YAML.parse()` to parse string
- Validate with `SpecificationSchema.parse()`
- Handle errors gracefully with `SpecificationError`

#### `lib/core/code-generator.ts`
Generates TypeScript code using OpenRouter.
- Load prompt template from `templates/prompts/`
- Populate template with spec details
- Call OpenRouter API
- Extract code from response
- Handle retries for API failures

#### `lib/verification/z3-generator.ts`
Converts spec to Z3 SMT-LIB format.
- Map spec params to Z3 constants (declare-const)
- Translate preconditions to Z3 assertions
- Generate postcondition checks
- Translate invariants to Z3 predicates
- Handle dynamic array access (enumerate all cases)
- Convert operators to SMT-LIB prefix notation
- Serialize to SMT-LIB string

**Key Functions**:
- `generateZ3Module(spec)`: Main entry point
- `generateConstants(spec)`: Generate variable declarations
- `translateConditionToZ3(condition, spec, isPostcondition)`: Convert YAML conditions to SMT-LIB
- `enumerateDynamicArrayAccess(condition, spec, isPostcondition)`: Handle `state[param]` access
- `translateOperatorsToSMTLib(expr)`: Convert infix to prefix notation
- `z3ModuleToString(module)`: Serialize to SMT-LIB

#### `lib/verification/z3-runner.ts`
Executes Z3 solver using z3-solver npm package.
- Initialize z3-solver with WASM
- Load SMT-LIB constraints
- Run solver (check-sat)
- Parse result (sat/unsat/unknown)
- Extract model if sat
- Return structured result

**Key Functions**:
- `runZ3(smtLib)`: Main entry point
- `parseSatResult(model)`: Extract counterexample values

#### `lib/verification/counterexample-parser.ts`
Parses Z3 model output.
- Extract violated constraint name
- Parse variable assignments from model
- Convert to structured `CounterExample`
- Generate human-readable suggested fix

---

## Implementation Guide

### 1. Implementing `spec-parser.ts`

```typescript
import YAML from 'yaml';
import { Specification, SpecificationSchema } from '@/lib/types/specification';
import { SpecificationError } from '@/lib/utils/errors';

export function parseSpec(yamlString: string): Specification {
  try {
    // Parse YAML
    const parsed = YAML.parse(yamlString);

    // Validate with Zod
    const spec = SpecificationSchema.parse(parsed);

    return spec;
  } catch (error) {
    if (error instanceof YAML.YAMLParseError) {
      throw new SpecificationError(`YAML parsing failed: ${error.message}`);
    }
    if (error instanceof z.ZodError) {
      const messages = error.errors.map(e => `${e.path.join('.')}: ${e.message}`);
      throw new SpecificationError(`Validation failed:\n${messages.join('\n')}`);
    }
    throw new SpecificationError(`Unknown error: ${error}`);
  }
}
```

### 2. Implementing `code-generator.ts`

```typescript
import { readFile } from 'fs/promises';
import path from 'path';
import { Specification } from '@/lib/types/specification';
import { generateWithOpenRouter } from '@/lib/services/openrouter.service';
import { CodeGenerationError } from '@/lib/utils/errors';

export async function generateCode(
  spec: Specification,
  feedback?: string
): Promise<string> {
  try {
    // Load appropriate prompt template
    const templateName = feedback ? 'code-repair.txt' : 'code-generation.txt';
    const templatePath = path.join(process.cwd(), 'templates', 'prompts', templateName);
    let template = await readFile(templatePath, 'utf-8');

    // Populate template
    template = template
      .replace('{{name}}', spec.name)
      .replace('{{signature}}', formatSignature(spec.signature))
      .replace('{{preconditions}}', spec.preconditions.map(p => `- ${p}`).join('\n'))
      .replace('{{postconditions}}', spec.postconditions.map(p => `- ${p}`).join('\n'))
      .replace('{{invariants}}', spec.invariants.map(i => `- ${i.type}`).join('\n'))
      .replace('{{delivery}}', spec.faultModel.delivery)
      .replace('{{reorder}}', String(spec.faultModel.reorder))
      .replace('{{crash_restart}}', String(spec.faultModel.crash_restart));

    if (feedback) {
      template = template.replace('{{violation}}', feedback);
    }

    // Call LLM
    const code = await generateWithOpenRouter(template);

    // Extract code from markdown if wrapped
    const codeMatch = code.match(/```typescript\n([\s\S]*?)\n```/);
    return codeMatch ? codeMatch[1] : code;
  } catch (error) {
    throw new CodeGenerationError(`Failed to generate code: ${error}`);
  }
}

function formatSignature(sig: FunctionSignature): string {
  const params = sig.params.map(p => `${p.name}: ${p.type}`).join(', ');
  return `(${params}) -> ${sig.returnType}`;
}
```

### 3. Implementing `z3-generator.ts`

Key steps:
1. Create Z3 constants from spec params and state variables
2. Generate balance variables (before and after state)
3. Generate processed request tracking (for idempotency)
4. Translate preconditions to Z3 assertions
5. Translate postconditions to Z3 assertions
6. Generate invariant constraints
7. Generate fault model constraints
8. Serialize to SMT-LIB format

**Example for conservation invariant**:
```typescript
function generateConservationConstraint(spec: Specification): Z3Constraint {
  const numAccounts = spec.bounds?.accts || 3;

  const beforeSum = Array.from({ length: numAccounts }, (_, i) => `balance_a${i + 1}`).join(' ');
  const afterSum = Array.from({ length: numAccounts }, (_, i) => `balance_a${i + 1}_after`).join(' ');

  const formula = `(= (+ ${beforeSum}) (+ ${afterSum}))`;

  return {
    name: 'Conservation',
    formula,
    description: 'Total resources must be conserved',
    type: 'invariant',
  };
}
```

**Key Challenge: Dynamic Array Access**

When spec contains `state[from] >= amt` where `from` is a parameter:
- Cannot directly represent in Z3 (requires array theory or enumeration)
- Solution: Enumerate all possible values based on `bounds.accts`

```typescript
// Input: "state[from] >= amt"
// Output: "(or (and (= from 1) (>= balance_a1 amt))
//              (and (= from 2) (>= balance_a2 amt))
//              (and (= from 3) (>= balance_a3 amt)))"
```

**Key Challenge: Operator Translation**

SMT-LIB uses prefix notation, not infix:
```typescript
// Input: "balance_a1 >= amt"
// Output: "(>= balance_a1 amt)"

// Input: "from != to"
// Output: "(distinct from to)"

// Input: "amt >= 0 && from != to"
// Output: "(and (>= amt 0) (distinct from to))"
```

### 4. Implementing `z3-runner.ts`

```typescript
import { init, Z3 } from 'z3-solver';
import { Z3Result } from '@/lib/types/verification';
import { logger } from '@/lib/utils/logger';

export async function runZ3(smtLib: string): Promise<Z3Result> {
  try {
    // Initialize Z3
    const { Context } = await init();
    const ctx = Context('main');
    const solver = new ctx.Solver();

    // Parse SMT-LIB
    solver.fromString(smtLib);

    // Check satisfiability
    const result = await solver.check();

    logger.debug('Z3 result', { result: result });

    if (result === 'unsat') {
      // Code is verified!
      return {
        success: true,
        result: 'unsat',
        constraintsChecked: extractConstraints(smtLib),
      };
    } else if (result === 'sat') {
      // Bug found - extract model
      const model = solver.model();

      return {
        success: false,
        result: 'sat',
        counterExample: parseCounterExample(model),
        model: model.toString(),
      };
    } else {
      // Unknown
      return {
        success: false,
        result: 'unknown',
        error: 'Z3 returned unknown (timeout or too complex)',
      };
    }
  } catch (error) {
    logger.error('Z3 execution failed', { error });
    throw new VerificationError(`Z3 execution failed: ${error}`);
  }
}

function extractConstraints(smtLib: string): string[] {
  const lines = smtLib.split('\n');
  return lines
    .filter(line => line.trim().startsWith('(assert'))
    .map(line => line.trim());
}

function parseCounterExample(model: any): CounterExample {
  // Extract variable assignments from Z3 model
  const assignments = model.entries().map(([name, value]) => ({
    variable: name,
    value: value.toString(),
  }));

  return {
    violatedConstraint: 'Unknown',
    trace: assignments,
    suggestedFix: 'Check the model values to identify the bug',
  };
}
```

### 5. Implementing `cegis-loop.ts`

```typescript
export async function runCEGISLoop(
  spec: Specification,
  maxIterations: number = 8
): Promise<VerificationResult> {
  const iterationHistory: IterationRecord[] = [];
  let currentCode: string | null = null;
  let feedback: string | undefined = undefined;

  for (let i = 1; i <= maxIterations; i++) {
    logger.info(`CEGIS iteration ${i}/${maxIterations}`);

    // 1. Generate code
    currentCode = await generateCode(spec, feedback);

    // 2. Generate Z3 constraints
    const z3Module = generateZ3Module(spec);
    const smtLib = z3ModuleToString(z3Module);

    // 3. Run Z3
    const z3Result = await runZ3(smtLib);

    // Record iteration
    iterationHistory.push({
      iteration: i,
      code: currentCode,
      z3Spec: smtLib,
      z3Result,
      feedback,
    });

    // 4. Check result
    if (z3Result.success && z3Result.result === 'unsat') {
      // Verification succeeded!
      return {
        success: true,
        iterations: i,
        finalCode: currentCode,
        z3Spec: smtLib,
        proofReport: generateProofReport(z3Result, spec),
        iterationHistory,
      };
    }

    // 5. Extract counterexample and generate feedback
    if (z3Result.counterExample) {
      feedback = generateRepairFeedback(z3Result.counterExample);
    } else {
      feedback = z3Result.model || 'Z3 found a violation but no model available';
    }
  }

  // Max iterations reached without success
  return {
    success: false,
    iterations: maxIterations,
    error: 'Max iterations reached without finding correct implementation',
    iterationHistory,
  };
}
```

---

## Testing Strategy

### Unit Tests

Test individual functions in isolation:

```typescript
// tests/unit/spec-parser.test.ts
describe('spec-parser', () => {
  it('should parse valid YAML', () => {
    const spec = parseSpec(validYaml);
    expect(spec.name).toBe('transfer_atomic');
  });

  it('should throw on invalid YAML', () => {
    expect(() => parseSpec(invalidYaml)).toThrow(SpecificationError);
  });
});

// tests/unit/z3-generator.test.ts
describe('z3-generator', () => {
  it('should generate valid SMT-LIB', () => {
    const spec = parseSpec(transferYaml);
    const module = generateZ3Module(spec);
    const smtLib = z3ModuleToString(module);

    expect(smtLib).toContain('(declare-const balance_a1 Int)');
    expect(smtLib).toContain('(assert');
  });

  it('should translate operators correctly', () => {
    const translated = translateOperatorsToSMTLib('balance >= amt');
    expect(translated).toBe('(>= balance amt)');
  });
});
```

### Integration Tests

Test the full CEGIS loop:

```typescript
// tests/integration/cegis-loop.test.ts
describe('cegis-loop', () => {
  it('should verify simple idempotent write', async () => {
    const spec = parseSpec(await readFile('fixtures/idempotent-write.yaml'));
    const result = await runCEGISLoop(spec, 5);

    expect(result.success).toBe(true);
    expect(result.finalCode).toBeDefined();
    expect(result.proofReport).toBeDefined();
  }, 60000); // 60s timeout
});
```

### Testing Z3 Generation

Create known-good Z3 specs and verify they return `unsat`:

```typescript
it('should generate Z3 that returns unsat', async () => {
  const spec = parseSpec(transferSpec);
  const z3Module = generateZ3Module(spec);
  const smtLib = z3ModuleToString(z3Module);

  const z3Result = await runZ3(smtLib);
  expect(z3Result.result).toBe('unsat');
  expect(z3Result.success).toBe(true);
});
```

---

## Common Tasks

### Adding a New Invariant Type

1. Add to Zod schema in `lib/types/specification.ts`:
```typescript
export const InvariantTypeSchema = z.enum([
  'idempotent',
  'no_double_spend',
  'atomic_no_partial_commit',
  'conservation',
  'my_new_invariant' // Add here
]);
```

2. Add Z3 constraint generation in `lib/verification/z3-generator.ts`:
```typescript
function generateInvariantConstraints(spec: Specification): Z3Constraint[] {
  const constraints: Z3Constraint[] = [];

  for (const invariant of spec.invariants) {
    switch (invariant.type) {
      case 'my_new_invariant':
        constraints.push(generateMyNewInvariantConstraint(spec, invariant));
        break;
      // ... other cases
    }
  }

  return constraints;
}

function generateMyNewInvariantConstraint(
  spec: Specification,
  inv: Invariant
): Z3Constraint {
  return {
    name: 'MyNewInvariant',
    formula: '(assert ...)', // Your Z3 formula
    description: 'Description of invariant',
    type: 'invariant',
  };
}
```

3. Add test:
```typescript
it('should verify my_new_invariant', async () => {
  const spec = parseSpec(yamlWithMyInvariant);
  const result = await runCEGISLoop(spec, 5);
  expect(result.success).toBe(true);
});
```

4. Update prompt template in `templates/prompts/code-generation.txt`

### Adding a New Fault Scenario

1. Update `FaultModel` type in `lib/types/specification.ts`
2. Add constraint generation in `z3-generator.ts`:
```typescript
if (spec.faultModel.network_partition) {
  constraints.push({
    name: 'NetworkPartition',
    formula: '(assert (or connected (not connected)))',
    description: 'Network can partition',
    type: 'transition',
  });
}
```

3. Include in fault model constraints generation

### Debugging Z3 Generation

1. Enable Z3 output writing:
```typescript
await writeFile('debug-output.smt2', smtLib);
```

2. Test Z3 directly:
```bash
pnpm tsx scripts/test-z3.ts
```

3. Check Z3 output for syntax errors or logical issues

4. Validate SMT-LIB syntax manually or with online Z3 playground

### Improving LLM Code Generation

1. Update prompts in `templates/prompts/`
2. Add more context about fault scenarios
3. Include code examples in prompts
4. Use few-shot learning with working examples
5. Add explicit instructions for idempotency patterns

---

## Important Constraints

### Security
- **Never execute generated code** directly on the server
- Validate all user inputs with Zod schemas
- Sanitize specs before Z3 execution
- Use WASM isolation for Z3 solver

### Performance
- Z3 can be **slow** for complex constraints
- Use `bounds` wisely (small values: 2-5)
- Timeout Z3 after 60 seconds
- Cache verified specs (future enhancement)

### LLM Limitations
- GPT-4 may not generate correct code on first try
- Need **counterexample feedback** for repair
- Max 8 iterations to prevent infinite loops
- Token limits: keep prompts < 8K tokens

### Z3 Constraints
- Z3 works best with **finite domains**
- Must bound all sets (accounts, retries, messages)
- Some invariants are **undecidable** (use approximations)
- SMT-LIB syntax is strict (test generated formulas!)

---

## Resources

### Z3 & SMT Solver Learning
- [Z3 Guide](https://rise4fun.com/z3/tutorial) - Official tutorial
- [SMT-LIB Standard](https://smtlib.cs.uiowa.edu/) - SMT-LIB format
- [z3-solver npm](https://www.npmjs.com/package/z3-solver) - JavaScript bindings

### Distributed Systems Patterns
- [Designing Data-Intensive Applications](https://dataintensive.net/) - Martin Kleppmann
- [Patterns of Distributed Systems](https://martinfowler.com/articles/patterns-of-distributed-systems/) - Unmesh Joshi

### CEGIS Papers
- [Syntax-Guided Synthesis](https://people.csail.mit.edu/asolar/SynthesisCourse/index.htm) - Course materials
- [Program Synthesis](https://www.microsoft.com/en-us/research/wp-content/uploads/2017/10/program_synthesis_now.pdf) - Gulwani et al.

### Next.js & TypeScript
- [Next.js Docs](https://nextjs.org/docs)
- [TypeScript Handbook](https://www.typescriptlang.org/docs/handbook/intro.html)

---

## Development Workflow

### 1. Start Development Server
```bash
pnpm dev
```

### 2. Run Tests
```bash
pnpm test          # Run all tests
pnpm test:ui       # Open Vitest UI
```

### 3. Test Z3 Directly
```bash
pnpm tsx scripts/test-z3.ts
```

### 4. Implement a Feature

**Example: Implement spec-parser.ts**

1. Read `lib/types/specification.ts` to understand schema
2. Implement `parseSpec()` function with Zod validation
3. Write unit tests in `tests/unit/spec-parser.test.ts`
4. Test with fixtures from `tests/fixtures/`
5. Update this document if adding new concepts

### 5. Debug Issues

**Z3 generation issues:**
- Check generated SMT-LIB format
- Validate syntax with `pnpm tsx scripts/test-z3.ts`
- Add debug logging in `z3-generator.ts`
- Compare with working examples

**LLM generation issues:**
- Check prompt templates in `templates/prompts/`
- Add more context or examples
- Increase temperature for more creativity
- Decrease temperature for more determinism

**Verification failures:**
- Examine counterexample model
- Check if invariant is too strict
- Verify bounds are appropriate
- Ensure fault model matches spec

---

## Quick Reference

### Key Files by Task

| Task | File |
|------|------|
| Parse YAML spec | `lib/core/spec-parser.ts` |
| Generate code | `lib/core/code-generator.ts` |
| Orchestrate CEGIS | `lib/core/cegis-loop.ts` |
| Generate Z3 SMT-LIB | `lib/verification/z3-generator.ts` |
| Run Z3 solver | `lib/verification/z3-runner.ts` |
| Parse Z3 models | `lib/verification/counterexample-parser.ts` |
| Call OpenRouter | `lib/services/openrouter.service.ts` |

### Key Types

| Type | File | Purpose |
|------|------|---------|
| `Specification` | `types/specification.ts` | YAML spec structure |
| `Z3Module` | `types/z3-ast.ts` | Z3 AST |
| `VerificationResult` | `types/verification.ts` | CEGIS output |
| `Z3Result` | `types/verification.ts` | Z3 solver output |
| `CounterExample` | `types/verification.ts` | Bug model |

### Environment Variables

```bash
OPENROUTER_API_KEY=sk-or-your-key-here                 # Required
NEXT_PUBLIC_CLERK_PUBLISHABLE_KEY=pk_...           # Optional
CLERK_SECRET_KEY=sk_...                            # Optional
NODE_ENV=development|production                     # Auto-set
```

---

## Troubleshooting

### "Module not found" errors
- Run `pnpm install`
- Check `tsconfig.json` paths are correct
- Verify imports use `@/` alias

### Z3 WASM files not found
- Run `pnpm tsx scripts/copy-z3-wasm.ts`
- Check `public/z3/*.wasm` files exist
- Verify z3-solver package is installed

### Zod validation fails
- Check YAML structure matches `SpecificationSchema`
- Look at `templates/specs/` for valid examples
- Check error message for specific field issues

### OpenRouter API errors
- Verify API key is set in `.env.local`
- Check rate limits
- Try reducing prompt size
- Add retry logic with exponential backoff

### Z3 returns "unknown"
- Reduce bounds (fewer accounts/retries)
- Simplify constraints
- Increase timeout
- Check for unsupported SMT-LIB features

---

## Glossary

- **CEGIS**: Counter-Example Guided Inductive Synthesis
- **Z3**: SMT solver from Microsoft Research
- **SMT**: Satisfiability Modulo Theories
- **SMT-LIB**: Standard input format for SMT solvers
- **sat**: Satisfiable (counterexample exists = bug found)
- **unsat**: Unsatisfiable (no counterexample = verified)
- **Invariant**: Property that must hold in all states
- **Fault model**: Specification of failure scenarios
- **Idempotency**: Property that repeated execution has same effect as single execution
- **Conservation**: Property that total resources remain constant
- **Counterexample**: Model showing invariant violation
- **Synthesis**: Automatic program generation

---

*Last Updated: 2025-10-08 (Phase 1 Modernization)*
*Version: 2.0.0 - Z3 Architecture*
