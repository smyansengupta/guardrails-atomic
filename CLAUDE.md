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

**Guardrails: Atomic** is an AI-powered code generation assistant that produces distributed system handlers with **formal correctness guarantees** using CEGIS (Counter-Example Guided Inductive Synthesis) with TLA+ model checking.

### What Problem Does It Solve?

Writing correct distributed systems code is notoriously difficult. Common bugs include:
- Race conditions under message reordering
- Double-spending under duplicate delivery (at-least-once semantics)
- Partial state updates after crashes
- Idempotency violations

Guardrails: Atomic **automatically generates and verifies** TypeScript handlers that are proven correct under specified fault scenarios.

### Technology Stack

- **Frontend/Backend**: Next.js 14 (App Router)
- **Language**: TypeScript
- **Styling**: Tailwind CSS
- **Package Manager**: pnpm
- **LLM**: OpenRouter GPT-4
- **Formal Verification**: TLA+ with TLC model checker (Docker)
- **Testing**: Vitest
- **Authentication**: Clerk
- **Database**: MongoDB Atlas (user sessions & history)

---

## Core Concepts

### 1. CEGIS (Counter-Example Guided Inductive Synthesis)

CEGIS is an iterative synthesis approach:

1. **Synthesize**: Generate candidate code using LLM
2. **Verify**: Check code against formal specification using TLA+/TLC
3. **Counterexample**: If bugs found, extract execution trace showing violation
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
                    │  to TLA+     │
                    └──────┬───────┘
                            │
                            ▼
                    ┌──────────────┐     ┌─────────────┐
                    │     TLC      │────▶│  Verified!  │
                    │    Verify    │ ✓   └─────────────┘
                    └──────┬───────┘
                            │ ✗
                            ▼
                    ┌──────────────┐
                    │Counterexample│
                    └──────┬───────┘
                            │
                            ▼
                    ┌──────────────┐
                    │     LLM      │
                    │    Repair    │
                    └──────────────┘
```

### 2. TLA+ (Temporal Logic of Actions)

TLA+ is a formal specification language used to model and verify concurrent systems. Key concepts:

- **Variables**: System state (e.g., `balances`, `processed`)
- **Actions**: State transitions (e.g., `Transfer`, `DuplicateTransfer`)
- **Invariants**: Properties that must always hold (e.g., conservation, idempotency)
- **Temporal formulas**: Properties over execution traces

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
- **`no_double_spend`**: Resources cannot be spent twice
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
│     → Call OpenRouter with prompt       │
│     → Get TypeScript code           │
│                                     │
│  2. [tla-generator.ts]              │
│     → Convert spec to TLA+ AST      │
│     → Serialize to TLA+ string      │
│                                     │
│  3. [tlc-runner.ts]                 │
│     → Write TLA+ to file            │
│     → Run TLC in Docker             │
│     → Parse output                  │
│                                     │
│  4. If violations:                  │
│     [counterexample-parser.ts]      │
│     → Extract trace                 │
│     → Generate feedback             │
│     → Go to step 1 with feedback    │
│                                     │
│  5. If verified:                    │
│     → Return success + proof report │
└─────────────────────────────────────┘
      ↓
API Response to Frontend
```

#### Authentication & Session Management *(planned)*
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

#### Verification History Persistence *(planned)*
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
guardrails/
├── app/                          # Next.js App Router
│   ├── api/                      # API routes
│   │   ├── verify/               # Main verification endpoint
│   │   ├── validate/             # Spec validation endpoint
│   │   ├── examples/             # Example specs endpoint
│   │   ├── generate-spec/        # NL to YAML endpoint
│   │   ├── history/              # (planned) Fetch saved verification runs
│   │   └── auth/[...clerk]/      # Clerk webhooks & callbacks (planned)
│   ├── (auth)/                   # (planned) Clerk sign-in/up routes
│   │   ├── sign-in/              # Hosted UI wrapper
│   │   └── sign-up/
│   ├── dashboard/                # (planned) Authenticated views
│   │   └── history/              # Saved prompts & results
│   ├── verify/                   # Verification UI page
│   ├── examples/                 # Examples gallery page
│   ├── generate-spec/            # NL to YAML UI page
│   │   └── page.tsx
│   ├── layout.tsx                # Root layout with new Nav Bar
│   ├── page.tsx                  # Landing page
│   └── globals.css               # Global styles
│
├── components/               # React components
│   ├── SpecEditor.tsx        # YAML input
│   ├── CodeViewer.tsx        # Code display
│   ├── ProofReport.tsx       # Verification results
│   ├── IterationHistory.tsx  # CEGIS timeline
│   ├── TraceVisualizer.tsx   # Counterexample display
│   ├── SpecGenerator.tsx     # New: NL to YAML component
│   └── ui/                   # Base UI components
│
├── lib/                      # Core business logic
│   ├── core/                 # Main CEGIS logic
│   │   ├── cegis-loop.ts     # Orchestration
│   │   ├── spec-parser.ts    # YAML parsing
│   │   └── code-generator.ts # LLM code gen
│   ├── verification/         # TLA+ & verification
│   │   ├── tla-generator.ts  # Spec → TLA+
│   │   ├── tlc-runner.ts     # TLC execution
│   │   └── counterexample-parser.ts
│   ├── history/              # (planned) Persistence & queries
│   │   └── persistence.ts    # Upsert & fetch helpers
│   ├── db/                   # (planned) Database connections
│   │   └── mongodb.ts        # MongoDB Atlas client
│   ├── types/                # TypeScript types
│   │   ├── specification.ts
│   │   ├── tla-ast.ts
│   │   ├── verification.ts
│   │   └── api.ts
│   ├── services/             # External services
│   │   └── openrouter.service.ts
│   └── utils/                # Utilities
│       ├── logger.ts
│       └── errors.ts
│
├── templates/                # Templates for generation
│   ├── specs/                # Example YAML specs
│   ├── tla/                  # TLA+ templates
│   └── prompts/              # LLM prompts
│       ├── code-generation.txt
│       ├── code-repair.txt
│       └── spec-generation.txt # New: NL to YAML prompt
│
├── tests/                    # Test suite
│   ├── unit/                 # Unit tests
│   ├── integration/          # Integration tests
│   └── fixtures/             # Test data
│
└── docker/                   # Docker configuration
    ├── tlc/                  # TLC container
    └── docker-compose.yml
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
Defines verification results and TLC output structures.

Key types:
- `VerificationResult` - Final output of CEGIS loop
- `TLCResult` - Result from TLC model checker
- `CounterExample` - Bug trace with suggested fix
- `ProofReport` - Verification success summary

#### `lib/core/cegis-loop.ts`
**Main orchestrator**. Implements the CEGIS loop:
1. Initialize with spec
2. Loop until verified or max iterations:
   - Generate code (with optional feedback)
   - Generate TLA+ spec
   - Run TLC
   - If violations, extract counterexample and loop
   - If verified, return success
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

#### `lib/verification/tla-generator.ts`
Converts spec to TLA+ module.
- Map spec params to TLA+ constants/variables
- Translate preconditions to `Init` predicate
- Generate actions for function + fault scenarios
- Translate invariants to TLA+ predicates
- Serialize AST to TLA+ string

#### `lib/verification/tlc-runner.ts`
Executes TLC model checker.
- Write TLA+ spec to temp file
- Generate TLC config file (`.cfg`)
- Run Docker container with TLC
- Parse output for violations
- Extract state counts, timing, etc.

#### `lib/verification/counterexample-parser.ts`
Parses TLC error output.
- Extract violated invariant name
- Parse state trace
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
      template = template.replace('{{code}}', feedback); // Previous code
      template = template.replace('{{violation}}', feedback);
      // ... etc
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

### 3. Implementing `tla-generator.ts`

Key steps:
1. Create TLA+ constants from bounds (e.g., `Accts = {"a1", "a2", "a3"}`)
2. Create variables from spec params and tracking state
3. Generate `Init` predicate from preconditions
4. Generate main action from function signature
5. Generate fault scenario actions (duplicates, reordering, crashes)
6. Translate invariants to TLA+ predicates
7. Generate `Next` relation as disjunction of all actions

Example for idempotency:
```tla
Idempotent ==
    \A req_id \in processed :
        DuplicateAction(req_id) => UNCHANGED state
```

### 4. Implementing `tlc-runner.ts`

```typescript
import { exec } from 'child_process';
import { promisify } from 'util';
import { writeFile, mkdir } from 'fs/promises';
import path from 'path';

const execAsync = promisify(exec);

export async function runTLC(
  tlaSpec: string,
  configFile: string
): Promise<TLCResult> {
  const workDir = path.join(process.cwd(), 'tla-output', Date.now().toString());
  await mkdir(workDir, { recursive: true });

  const specPath = path.join(workDir, 'Spec.tla');
  const cfgPath = path.join(workDir, 'Spec.cfg');

  await writeFile(specPath, tlaSpec);
  await writeFile(cfgPath, configFile);

  try {
    const { stdout, stderr } = await execAsync(
      `docker run --rm -v ${workDir}:/workspace guardrails-tlc Spec.tla`,
      { timeout: 60000 } // 1 minute timeout
    );

    const output = stdout + stderr;

    // Parse TLC output
    const success = !output.includes('Error:');
    const statesMatch = output.match(/(\d+) states generated/);
    const statesExplored = statesMatch ? parseInt(statesMatch[1]) : 0;

    if (success) {
      return {
        success: true,
        statesExplored,
        invariantsChecked: extractInvariants(output),
        output,
      };
    } else {
      return {
        success: false,
        statesExplored,
        invariantsChecked: [],
        violations: parseViolations(output),
        counterExample: parseCounterExample(output),
        output,
      };
    }
  } catch (error) {
    throw new TLCExecutionError(`TLC execution failed: ${error}`);
  }
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

    // 2. Generate TLA+ spec
    const tlaModule = generateTLAModule(spec);
    const tlaSpec = tlaModuleToString(tlaModule);
    const configFile = generateTLCConfig(spec);

    // 3. Run TLC
    const tlcResult = await runTLC(tlaSpec, configFile);

    // Record iteration
    iterationHistory.push({
      iteration: i,
      code: currentCode,
      tlaSpec,
      tlcResult,
      feedback,
    });

    // 4. Check result
    if (tlcResult.success) {
      // Verification succeeded!
      return {
        success: true,
        iterations: i,
        finalCode: currentCode,
        tlaSpec,
        proofReport: generateProofReport(tlcResult, spec),
        iterationHistory,
      };
    }

    // 5. Extract counterexample and generate feedback
    if (tlcResult.counterExample) {
      feedback = generateRepairFeedback(tlcResult.counterExample);
    } else {
      feedback = tlcResult.output; // Fallback to raw output
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

### Testing TLA+ Generation

Create known-good TLA+ specs and verify they pass TLC:

```typescript
it('should generate TLA+ that passes TLC', async () => {
  const spec = parseSpec(transferSpec);
  const tlaModule = generateTLAModule(spec);
  const tlaString = tlaModuleToString(tlaModule);

  const tlcResult = await runTLC(tlaString, generateConfig(spec));
  expect(tlcResult.success).toBe(true);
});
```

---

## Common Tasks

### Adding a New Invariant Type

1. Add to Zod schema in `lib/types/specification.ts`:
```typescript
export const SpecificationSchema = z.object({
  // ...
  invariants: z.array(z.object({
    type: z.enum([
      'idempotent',
      'no_double_spend',
      'atomic_no_partial_commit',
      'conservation',
      'my_new_invariant' // Add here
    ]),
    // ...
  })),
});
```

2. Add TLA+ translation in `lib/verification/tla-generator.ts`:
```typescript
function translateInvariant(inv: Invariant): TLAInvariant {
  switch (inv.type) {
    case 'my_new_invariant':
      return {
        name: 'MyNewInvariant',
        predicate: '\\A x \\in Domain : Property(x)',
        description: 'Description of the invariant',
      };
    // ... other cases
  }
}
```

3. Update prompt template in `templates/prompts/code-generation.txt`

4. Add example spec in `templates/specs/`

### Adding a New Fault Scenario

1. Update `FaultModel` type in `lib/types/specification.ts`
2. Add action generation in `tla-generator.ts`:
```typescript
if (spec.faultModel.network_partition) {
  actions.push({
    name: 'NetworkPartition',
    guards: ['connected'],
    updates: ['connected\' = FALSE'],
    unchanged: ['state'],
  });
}
```

3. Include in `Next` relation:
```tla
Next ==
    \/ MainAction
    \/ DuplicateAction
    \/ NetworkPartition  \* New action
```

### Debugging TLA+ Generation

1. Enable TLA+ output writing:
```typescript
await writeFile('debug-output.tla', tlaSpec);
```

2. Run TLC manually:
```bash
docker run --rm -v $(pwd):/workspace guardrails-tlc debug-output.tla
```

3. Check TLC output for syntax errors or logical issues

4. Compare with working examples in `templates/tla/`

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
- Sanitize TLA+ specs before Docker execution
- Use read-only Docker volumes where possible

### Performance
- TLC can be **very slow** for large state spaces
- Use `bounds` wisely (small values: 2-5)
- Timeout TLC after 60 seconds
- Cache verified specs (future enhancement)

### LLM Limitations
- GPT-4 may not generate correct code on first try
- Need **counterexample feedback** for repair
- Max 8 iterations to prevent infinite loops
- Token limits: keep prompts < 8K tokens

### TLA+ Constraints
- TLC only explores **finite state spaces**
- Must bound all sets (accounts, retries, messages)
- Some invariants are **undecidable** (use approximations)
- TLC syntax is strict (test generated specs!)

---

## Resources

### TLA+ Learning
- [Learn TLA+](https://learntla.com/) - Excellent tutorial
- [TLA+ Examples](https://github.com/tlaplus/Examples) - Official examples
- [Practical TLA+](https://link.springer.com/book/10.1007/978-1-4842-3829-5) - Book by Hillel Wayne

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

### 3. Build Docker Images
```bash
cd docker
docker build -t guardrails-tlc tlc/
docker-compose up
```

### 4. Implement a Feature

**Example: Implement spec-parser.ts**

1. Read `lib/types/specification.ts` to understand schema
2. Implement `parseSpec()` function with Zod validation
3. Write unit tests in `tests/unit/spec-parser.test.ts`
4. Test with fixtures from `tests/fixtures/`
5. Update this document if adding new concepts

### 5. Debug Issues

**TLA+ generation issues:**
- Check `templates/tla/Transfer.tla` for working example
- Validate TLA+ syntax with TLC manually
- Add debug logging in `tla-generator.ts`

**LLM generation issues:**
- Check prompt templates in `templates/prompts/`
- Add more context or examples
- Increase temperature for more creativity
- Decrease temperature for more determinism

**Verification failures:**
- Examine counterexample trace
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
| Generate TLA+ | `lib/verification/tla-generator.ts` |
| Run TLC | `lib/verification/tlc-runner.ts` |
| Parse errors | `lib/verification/counterexample-parser.ts` |
| Call OpenRouter | `lib/services/openrouter.service.ts` |

### Key Types

| Type | File | Purpose |
|------|------|---------|
| `Specification` | `types/specification.ts` | YAML spec structure |
| `TLAModule` | `types/tla-ast.ts` | TLA+ AST |
| `VerificationResult` | `types/verification.ts` | CEGIS output |
| `TLCResult` | `types/verification.ts` | TLC output |
| `CounterExample` | `types/verification.ts` | Bug trace |

### Environment Variables

```bash
OPENROUTER_API_KEY=sk-or-your-key-here                 # Required
NEXT_PUBLIC_CLERK_PUBLISHABLE_KEY=pk_...           # Optional
CLERK_SECRET_KEY=sk_...                            # Optional
TLC_DOCKER_IMAGE=guardrails-tlc                    # Default
NODE_ENV=development|production                     # Auto-set
```

---

## Troubleshooting

### "Module not found" errors
- Run `pnpm install`
- Check `tsconfig.json` paths are correct
- Verify imports use `@/` alias

### TLC Docker fails
- Build TLC image: `cd docker/tlc && docker build -t guardrails-tlc .`
- Check Docker is running
- Verify volume mounts are correct

### Zod validation fails
- Check YAML structure matches `SpecificationSchema`
- Look at `templates/specs/` for valid examples
- Check error message for specific field issues

### OpenRouter API errors
- Verify API key is set in `.env.local`
- Check rate limits
- Try reducing prompt size
- Add retry logic with exponential backoff

---

## Next Steps for Implementation

### Phase 1: Core Parsing (Priority 1)
- [ ] Implement `spec-parser.ts` with full Zod validation
- [ ] Add comprehensive error messages
- [ ] Test with all example specs

### Phase 2: TLA+ Generation (Priority 1)
- [ ] Implement `tla-generator.ts` for basic specs
- [ ] Support all invariant types
- [ ] Test generated TLA+ manually with TLC

### Phase 3: TLC Integration (Priority 1)
- [ ] Implement `tlc-runner.ts` with Docker
- [ ] Parse TLC output correctly
- [ ] Extract counterexamples

### Phase 4: LLM Integration (Priority 2)
- [ ] Implement OpenRouter service wrapper
- [ ] Create prompt templates
- [ ] Add retry logic

### Phase 5: CEGIS Loop (Priority 2)
- [ ] Implement full `cegis-loop.ts`
- [ ] Add iteration history tracking
- [ ] Generate proof reports

### Phase 6: UI Polish (Priority 3)
- [ ] Add syntax highlighting to editors
- [ ] Improve trace visualization
- [ ] Add real-time progress updates

### Phase 7: Optimizations (Priority 3)
- [ ] Cache verified specs
- [ ] Parallel TLC execution
- [ ] Incremental verification

### Phase 8: Auth & History (Priority 1)
- [ ] Integrate Clerk middleware for protected routes
- [ ] Create sign-in/up routes under `app/(auth)/`
- [ ] Persist verification runs to MongoDB Atlas
- [ ] Build history dashboard + `/api/history`

---

## Contributing Guidelines

### Code Style
- Use TypeScript strict mode
- Add JSDoc comments to all exported functions
- Use meaningful variable names
- Prefer functional programming patterns

### Error Handling
- Use custom error classes from `utils/errors.ts`
- Always provide context in error messages
- Log errors with `logger.error()`

### Testing
- Write tests before implementing (TDD)
- Aim for >80% code coverage
- Use fixtures for complex test data
- Mock external services (OpenRouter, Docker)

### Documentation
- Update this file when adding new concepts
- Add inline comments for complex logic
- Keep README.md user-focused
- Document all breaking changes

---

## Glossary

- **CEGIS**: Counter-Example Guided Inductive Synthesis
- **TLA+**: Temporal Logic of Actions (specification language)
- **TLC**: TLA+ model checker
- **Invariant**: Property that must hold in all states
- **Fault model**: Specification of failure scenarios
- **Idempotency**: Property that repeated execution has same effect as single execution
- **Conservation**: Property that total resources remain constant
- **State space**: All possible system states
- **Counterexample**: Execution trace showing invariant violation
- **Synthesis**: Automatic program generation

---

*Last Updated: 2025-10-04*
*Version: 1.0.0*
