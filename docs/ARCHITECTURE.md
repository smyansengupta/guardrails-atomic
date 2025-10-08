# Guardrails: Atomic - Architecture Guide

## Table of Contents
1. [System Overview](#system-overview)
2. [Core Concepts](#core-concepts)
3. [Architecture](#architecture)
4. [Data Flow](#data-flow)
5. [Z3 SMT Solver Integration](#z3-smt-solver-integration)
6. [CEGIS Loop](#cegis-loop)
7. [Technology Stack](#technology-stack)

---

## System Overview

**Guardrails: Atomic** is an AI-powered code generation tool that produces formally verified distributed system handlers using Counter-Example Guided Inductive Synthesis (CEGIS) with the Z3 SMT solver.

### What Problem Does It Solve?

Writing correct distributed systems code is notoriously difficult. Common bugs include:
- Race conditions under message reordering
- Double-spending under duplicate delivery (at-least-once semantics)
- Partial state updates after crashes
- Idempotency violations

Guardrails: Atomic **automatically generates and verifies** TypeScript handlers that are proven correct under specified fault scenarios.

---

## Core Concepts

### CEGIS (Counter-Example Guided Inductive Synthesis)

CEGIS is an iterative synthesis approach:

1. **Synthesize**: Generate candidate code using LLM
2. **Verify**: Check code against formal specification using Z3
3. **Counterexample**: If bugs found, extract execution trace showing violation
4. **Refine**: Use counterexample to guide LLM to fix the code
5. **Repeat**: Continue until verified or max iterations reached

```
User YAML Spec
      ↓
┌─────────────────────────────────┐
│  CEGIS Loop (max 8 iterations) │
│                                 │
│  1. LLM Generate Code           │
│  2. Translate to Z3 Constraints │
│  3. Run Z3 Solver               │
│  4. If 'sat' (bug) → Extract    │
│     counterexample → Repair     │
│  5. If 'unsat' (verified) → ✅  │
└─────────────────────────────────┘
      ↓
Formally Verified TypeScript Code
```

### Z3 SMT Solver

Z3 is a high-performance theorem prover from Microsoft Research. It uses **Satisfiability Modulo Theories** (SMT) to verify program properties.

**Key Concept**: Z3 searches for counterexamples
- `sat` = Found a counterexample = **BUG EXISTS** ❌
- `unsat` = No counterexample exists = **CODE IS CORRECT** ✅
- `unknown` = Z3 couldn't decide (timeout or too complex)

### Fault Models

The system supports various fault scenarios:
- **Delivery semantics**: `at_least_once`, `exactly_once`, `at_most_once`
- **Message reordering**: Messages can arrive out of order
- **Crash/restart**: Process can crash and restart, losing in-memory state

### Invariants

Supported invariant types:
- **`idempotent`**: Repeated execution with same request ID has no additional effect
- **`no_double_spend`**: Resources cannot be spent twice
- **`atomic_no_partial_commit`**: Either all state changes happen or none
- **`conservation`**: Total amount of resources remains constant

---

## Architecture

### High-Level Components

```
┌─────────────────────────────────────────────────────────┐
│                    Frontend (Next.js)                    │
│  ┌──────────────┐  ┌──────────────┐  ┌───────────────┐ │
│  │ Spec Editor  │  │ Code Viewer  │  │ Proof Report  │ │
│  └──────────────┘  └──────────────┘  └───────────────┘ │
└────────────────────────┬────────────────────────────────┘
                         │ HTTP / SSE
┌────────────────────────▼────────────────────────────────┐
│                    API Routes (Next.js)                  │
│  /api/verify  /api/generate-spec  /api/generate-code    │
└────────────────────────┬────────────────────────────────┘
                         │
┌────────────────────────▼────────────────────────────────┐
│                    Core Business Logic                   │
│  ┌──────────────┐  ┌──────────────┐  ┌───────────────┐ │
│  │ CEGIS Loop   │  │ Code Gen     │  │ Z3 Generator  │ │
│  └──────────────┘  └──────────────┘  └───────────────┘ │
└────────────────────────┬────────────────────────────────┘
                         │
         ┌───────────────┴───────────────┐
         │                               │
┌────────▼─────────┐           ┌────────▼────────┐
│  OpenRouter API  │           │   Z3 Solver     │
│  (LLM: GPT-4)    │           │   (z3-solver)   │
└──────────────────┘           └─────────────────┘
         │                               │
         └───────────────┬───────────────┘
                         │
┌────────────────────────▼────────────────────────────────┐
│               Persistence Layer (MongoDB)                │
│          Clerk Authentication │ Verification History     │
└─────────────────────────────────────────────────────────┘
```

### Directory Structure

```
guardrails-atomic/
├── app/                        # Next.js App Router
│   ├── api/                    # API routes
│   │   ├── verify/             # Main verification endpoint
│   │   ├── generate-spec/      # NL to YAML
│   │   ├── generate-code/      # Code generation only
│   │   └── generate-tla/       # Z3 constraints only (misnamed, TODO: rename)
│   ├── verify/                 # Verification UI page
│   ├── examples/               # Examples gallery
│   └── history/                # Verification history
│
├── components/                 # React components
│   ├── SpecEditor.tsx          # YAML input
│   ├── CodeViewer.tsx          # Code display
│   ├── ProofReport.tsx         # Verification results
│   └── IterationHistory.tsx    # CEGIS timeline
│
├── lib/                        # Core business logic
│   ├── core/                   # Main CEGIS logic
│   │   ├── cegis-loop.ts       # Orchestration
│   │   ├── spec-parser.ts      # YAML parsing
│   │   └── code-generator.ts   # LLM code generation
│   ├── verification/           # Z3 verification
│   │   ├── z3-generator.ts     # Spec → Z3 SMT constraints
│   │   ├── z3-runner.ts        # Z3 execution
│   │   └── counterexample-parser.ts (TBD)
│   ├── services/               # External services
│   │   └── openrouter.service.ts
│   ├── history/                # Persistence
│   │   └── persistence.ts
│   ├── db/                     # Database
│   │   └── mongodb.ts
│   └── types/                  # TypeScript types
│       ├── specification.ts
│       ├── verification.ts
│       └── z3-ast.ts
│
├── templates/                  # Templates
│   ├── specs/                  # Example YAML specs
│   └── prompts/                # LLM prompts
│
├── tests/                      # Test suite
│   ├── unit/                   # Unit tests
│   └── integration/            # Integration tests
│
├── docs/                       # Documentation
│   ├── ARCHITECTURE.md         # This file
│   ├── DEVELOPMENT.md          # Developer guide
│   └── API.md                  # API reference
│
└── scripts/                    # Build scripts
    ├── copy-z3-wasm.ts         # Copy Z3 WASM files
    └── watch-and-copy-z3.ts    # Watch mode

```

---

## Data Flow

### Natural Language to YAML Specification

```
1. User enters natural language description
2. POST /api/generate-spec
3. OpenRouter API (GPT-4) generates YAML spec
4. User reviews and edits YAML in editor
5. User proceeds to verification
```

### Verification Flow

```
1. User submits YAML spec
2. POST /api/verify
3. Parse YAML → Specification object (Zod validation)
4. Enter CEGIS loop:

   For each iteration (max 8):
   ├─ Call OpenRouter: Generate TypeScript code
   ├─ Generate Z3 constraints from spec
   ├─ Run Z3 solver
   ├─ If 'sat' (bug found):
   │  ├─ Extract counterexample from Z3 model
   │  ├─ Generate repair feedback
   │  └─ Loop back with feedback
   └─ If 'unsat' (verified):
      ├─ Generate proof report
      ├─ Save to MongoDB
      └─ Return success with verified code

5. Stream progress updates via SSE (optional)
6. Display results to user
```

---

## Z3 SMT Solver Integration

### SMT-LIB Format

Z3 accepts constraints in SMT-LIB format:

```smt
; Declare variables
(declare-const balance_a1 Int)
(declare-const balance_a2 Int)
(declare-const from Int)
(declare-const to Int)
(declare-const amt Int)

; Assert constraints
(assert (>= balance_a1 0))  ; Non-negative balance
(assert (distinct from to))  ; Different accounts
(assert (>= balance_a1 amt)) ; Sufficient funds

; Check for counterexamples
(check-sat)  ; Returns 'sat' (bug) or 'unsat' (correct)
(get-model)  ; If 'sat', get values that trigger bug
```

### Constraint Generation

The `z3-generator.ts` module translates YAML specs to SMT-LIB:

1. **Generate constants**: Create variables for accounts, balances, parameters
2. **Translate preconditions**: Convert to Z3 assertions
3. **Translate postconditions**: Convert to Z3 assertions
4. **Generate invariants**: Idempotency, conservation, etc.
5. **Handle dynamic array access**: Enumerate all possible values
6. **Serialize to SMT-LIB**: Output as string

#### Example: Dynamic Array Access

Input: `state[from] >= amt`

Problem: `from` is a variable, Z3 needs concrete values

Solution: Enumerate all possibilities:
```smt
(or
  (and (= from 1) (>= balance_a1 amt))
  (and (= from 2) (>= balance_a2 amt))
  (and (= from 3) (>= balance_a3 amt))
)
```

### Z3 Execution

The `z3-runner.ts` module:
1. Initializes Z3 solver using `z3-solver` npm package
2. Parses SMT-LIB commands
3. Declares constants
4. Adds assertions
5. Calls `solver.check()` → `sat` / `unsat` / `unknown`
6. If `sat`, extracts model with `solver.model()`
7. Returns result with counterexample

---

## CEGIS Loop

### Iteration Structure

Each CEGIS iteration consists of 4 phases:

**Phase 1: Code Generation**
- Load prompt template (`code-generation.txt` or `code-repair.txt`)
- Populate with spec details
- Call OpenRouter API (GPT-4)
- Extract TypeScript code from markdown

**Phase 2: Z3 Constraint Generation**
- Generate constants for all variables
- Translate preconditions → Z3 assertions
- Translate postconditions → Z3 assertions
- Generate invariant constraints
- Serialize to SMT-LIB format

**Phase 3: Z3 Verification**
- Initialize Z3 solver
- Execute SMT-LIB commands
- Check satisfiability
- Extract model if `sat`

**Phase 4: Feedback Generation** (if `sat`)
- Parse counterexample from Z3 model
- Format as human-readable trace
- Generate suggested fix
- Feed back to Phase 1 for repair

### Termination Conditions

The loop terminates when:
- ✅ Z3 returns `unsat` (verification succeeds)
- ❌ Max iterations reached (default: 8)
- ❌ Error occurs (parsing, LLM failure, Z3 timeout)

### Success Example

```
Iteration 1: sat (Bug: insufficient balance check)
Iteration 2: sat (Bug: idempotency violation)
Iteration 3: unsat ✅ VERIFIED!

Result:
- Formally verified TypeScript code
- Proof report with guarantees
- Iteration history with traces
```

---

## Technology Stack

- **Frontend/Backend**: Next.js 15 (App Router), React 19
- **Language**: TypeScript (100% TypeScript codebase)
- **Formal Verification**: Z3 SMT Solver (`z3-solver` npm package)
- **LLM Integration**: OpenRouter API (GPT-4)
- **Authentication**: Clerk
- **Database**: MongoDB Atlas
- **Testing**: Vitest
- **Styling**: Tailwind CSS
- **Package Manager**: pnpm

### Why Z3?

- **Mature**: 15+ years of research at Microsoft
- **Fast**: Highly optimized C++ implementation
- **Expressive**: Supports integers, arrays, uninterpreted functions
- **JavaScript Integration**: `z3-solver` npm package with WASM build
- **No Docker Required**: Runs in-process via WebAssembly

### Migration from TLA+

This project was originally designed to use TLA+ with the TLC model checker. We migrated to Z3 for the following reasons:

1. **Better JavaScript integration**: Z3 has native WASM bindings
2. **Faster verification**: Z3 uses SMT solving instead of exhaustive state exploration
3. **Simpler deployment**: No Docker containers required
4. **Better constraint handling**: SMT theories are more expressive

All TLA+ code has been removed as of Phase 1 modernization.

---

## Performance Considerations

### Z3 Solver Performance

- **Typical verification time**: 100-500ms
- **Timeout**: 60 seconds per iteration
- **State space**: Bounded by `bounds` in spec (accts: 3, retries: 2)

### LLM Code Generation

- **Typical generation time**: 2-10 seconds
- **Model**: GPT-4 via OpenRouter
- **Token limit**: ~8K tokens per prompt

### Optimization Strategies

1. **Keep bounds small**: `accts: 3` instead of `accts: 10`
2. **Cache verified specs**: (TODO) Store verified code
3. **Parallel verification**: (TODO) Run multiple candidates
4. **Incremental verification**: (TODO) Only verify changed parts

---

## Security Considerations

### Safe Code Generation

- **Never execute generated code**: Only verify formally
- **Sandbox Z3**: WASM sandboxing prevents file system access
- **Validate all inputs**: Zod schemas for all API requests

### Authentication

- **Clerk-based auth**: Secure JWT tokens
- **User-scoped API keys**: (TODO) Users bring their own OpenRouter keys
- **MongoDB security**: Atlas with IP whitelisting, TLS

---

## Future Enhancements

### Planned Features

1. **User API Keys**: Let users provide their own OpenRouter/OpenAI keys
2. **Caching**: Cache verified implementations to avoid re-verification
3. **More invariants**: Support custom invariants via predicates
4. **Multi-language**: Generate code in Python, Go, Rust
5. **Real-time collaboration**: Multiple users working on same spec

### Research Directions

1. **Neural-guided synthesis**: Use ML to predict good candidates
2. **Compositional verification**: Verify modules independently
3. **Automatic fault model inference**: Learn fault models from tests

---

*Last Updated: 2025-10-08 (Phase 1 Modernization)*
