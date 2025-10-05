# API Structure Guide

Complete API structure for Guardrails: Atomic with all types, interfaces, and function signatures.

## Directory Structure

```
guardrails/
├── app/api/                    # Next.js API routes
│   ├── verify/
│   │   └── route.ts           # POST /api/verify - Run CEGIS loop
│   ├── validate/
│   │   └── route.ts           # POST /api/validate - Validate YAML spec
│   ├── examples/
│   │   └── route.ts           # GET /api/examples - Get example specs
│   └── generate-spec/
│       └── route.ts           # POST /api/generate-spec - NL to YAML
│
├── lib/
│   ├── types/                 # TypeScript type definitions
│   │   ├── specification.ts   # Spec types and Zod schemas
│   │   ├── verification.ts    # Verification result types
│   │   ├── tla-ast.ts        # TLA+ AST types
│   │   └── api.ts            # API request/response types
│   │
│   ├── core/                  # Core business logic
│   │   ├── spec-parser.ts           # Parse YAML to Specification
│   │   ├── code-generator.ts        # Generate code from spec
│   │   └── cegis-loop.ts           # Main CEGIS orchestration
│   │
│   ├── verification/          # TLA+ verification logic
│   │   ├── tla-generator.ts         # Spec → TLA+ module
│   │   ├── tlc-runner.ts            # Execute TLC in Docker
│   │   └── counterexample-parser.ts # Parse TLC output
│   │
│   ├── services/              # External service integrations
│   │   └── openrouter.service.ts    # OpenRouter API wrapper
│   │
│   └── utils/                 # Utility functions
│       ├── errors.ts                # Custom error classes
│       └── logger.ts                # Logging utility
│
├── components/               # React components
│   ├── SpecEditor.tsx        # YAML input
│   ├── CodeViewer.tsx        # Code display
│   ├── ProofReport.tsx       # Verification results
│   ├── IterationHistory.tsx  # CEGIS timeline
│   ├── TraceVisualizer.tsx   # Counterexample display
│   └── ui/                   # ShadCN UI components
│
└── templates/
    └── prompts/              # LLM prompts
        ├── code-generation.txt
        ├── code-repair.txt
        └── spec-generation.txt
```

---

## API Routes

### 1. POST /api/verify
**File**: `app/api/verify/route.ts`

Run the complete CEGIS loop to verify a specification.

**Request** (`VerifyRequest`):
```typescript
{
  spec: string;              // YAML specification
  maxIterations?: number;    // Default: 8
}
```

**Response** (`VerifyResponse`):
```typescript
{
  success: boolean;
  result?: VerificationResult;  // See below
  error?: string;
}
```

---

### 2. POST /api/validate
**File**: `app/api/validate/route.ts`

Validate YAML spec without running verification.

**Request** (`ValidateRequest`):
```typescript
{
  spec: string;  // YAML specification
}
```

**Response** (`ValidateResponse`):
```typescript
{
  valid: boolean;
  errors?: string[];
  parsed?: Specification;
}
```

---

### 3. GET /api/examples
**File**: `app/api/examples/route.ts`

Get example specifications.

**Response** (`ExamplesResponse`):
```typescript
{
  examples: ExampleSpec[];
}

interface ExampleSpec {
  name: string;
  description: string;
  yaml: string;
  category: 'transfer' | 'write' | 'saga';
}
```

---

### 4. POST /api/generate-spec
**File**: `app/api/generate-spec/route.ts`

Convert natural language description to YAML spec.

**Request**:
```typescript
{
  naturalLanguage: string;  // Natural language description
}
```

**Response**:
```typescript
{
  yaml: string;        // Generated YAML spec
}
```

---

## Type Definitions

### lib/types/specification.ts

Core specification types with Zod validation.

**Key Types**:
- `Specification` - Complete spec structure
- `FunctionSignature` - Function params and return type
- `Invariant` - Invariant definition
- `FaultModel` - Fault scenario configuration
- `Bounds` - Model checking bounds

**Zod Schema**: `SpecificationSchema` - Use for runtime validation

---

### lib/types/verification.ts

Verification results and TLC output.

**Key Types**:
- `VerificationResult` - Final CEGIS result
- `IterationRecord` - Single CEGIS iteration
- `TLCResult` - TLC model checker output
- `CounterExample` - Bug trace with execution steps
- `ProofReport` - Verification success summary

---

### lib/types/tla-ast.ts

TLA+ Abstract Syntax Tree.

**Key Types**:
- `TLAModule` - Complete TLA+ module
- `TLAAction` - State transition
- `TLAInvariant` - TLA+ invariant
- `TLAConstant` - TLA+ constant
- `TLAVariable` - TLA+ variable

---

### lib/types/api.ts

API request/response types for all endpoints.

**Exports**:
- `VerifyRequest` / `VerifyResponse`
- `ValidateRequest` / `ValidateResponse`
- `ExampleSpec` / `ExamplesResponse`

---

## Core Services

### lib/core/spec-parser.ts

```typescript
export function parseSpec(yamlString: string): Specification
```

**Purpose**: Parse and validate YAML specification

---

### lib/core/code-generator.ts

```typescript
export async function generateCode(
  spec: Specification,
  feedback?: string
): Promise<string>
```

**Purpose**: Generate TypeScript code from specification using LLM

---

### lib/core/cegis-loop.ts

```typescript
export async function runCEGISLoop(
  spec: Specification,
  maxIterations: number = 8
): Promise<VerificationResult>
```

**Purpose**: Main CEGIS orchestration loop

---

## Verification Services

### lib/verification/tla-generator.ts

```typescript
export function generateTLAModule(spec: Specification): TLAModule

export function tlaModuleToString(module: TLAModule): string
```

**Purpose**: Convert specification to TLA+ module

---

### lib/verification/tlc-runner.ts

```typescript
export async function runTLC(
  tlaSpec: string,
  configFile: string
): Promise<TLCResult>
```

**Purpose**: Execute TLC model checker in Docker

---

### lib/verification/counterexample-parser.ts

```typescript
export function parseCounterExample(tlcOutput: string): CounterExample | null

export function parseViolations(tlcOutput: string): InvariantViolation[]
```

**Purpose**: Parse TLC error output into structured format

---

## External Services

### lib/services/openrouter.service.ts

```typescript
export async function generateWithOpenRouter(
  prompt: string,
  model: string = 'openai/gpt-4'
): Promise<string>
```

**Purpose**: Call OpenRouter API for text generation

---

## Utilities

### lib/utils/errors.ts

Custom error classes:

```typescript
export class SpecificationError extends Error
export class VerificationError extends Error
export class TLCExecutionError extends Error
export class CodeGenerationError extends Error
```

---

### lib/utils/logger.ts

Logging utility:

```typescript
export const logger = {
  info(message: string, meta?: any): void
  warn(message: string, meta?: any): void
  error(message: string, meta?: any): void
  debug(message: string, meta?: any): void
}
```

---

*Last Updated: 2025-10-04*
*Version: 1.0.1*