# Guardrails: Atomic

AI-powered code generation with formal correctness guarantees for distributed systems.

## Quick Start

### Prerequisites
- Node.js 20+
- pnpm package manager
- Docker & Docker Compose
- OpenRouter API key
- Clerk account (optional for MVP)

### Installation

1. Clone the repository:
```bash
git clone https://github.com/yourusername/guardrails-atomic.git
cd guardrails-atomic
```

2. Install dependencies:
```bash
pnpm install
```

3. Set up environment variables:
```bash
cp .env.local.example .env.local
# Edit .env.local with your API keys
```

4. Run development server:
```bash
pnpm dev
```

Open [http://localhost:3000](http://localhost:3000)

### Docker Deployment

```bash
cd docker
docker-compose up --build
```

## Project Structure

- `app/` - Next.js pages and API routes
- `components/` - React components
- `lib/` - Core business logic
  - `core/` - CEGIS loop, spec parsing, code generation
  - `verification/` - TLA+ generation, TLC execution
  - `types/` - TypeScript type definitions
- `templates/` - TLA+ modules, example specs, LLM prompts
- `tests/` - Unit and integration tests

## Testing

```bash
pnpm test
pnpm test:ui
```

## How It Works

1. **Specify**: Write a YAML specification defining your distributed system handler
2. **Generate**: AI generates TypeScript code from the specification
3. **Verify**: TLA+ model checker proves correctness under fault scenarios
4. **Repair**: If bugs are found, AI fixes them based on counterexamples
5. **Repeat**: Process continues until code is proven correct

## Example Specification

```yaml
name: transfer_atomic
signature:
  params:
    - name: state
      type: Map<Acct,int>
    - name: from
      type: Acct
    - name: to
      type: Acct
    - name: amt
      type: int
    - name: req_id
      type: UUID
  returnType: Map<Acct,int>
preconditions:
  - amt >= 0
  - from != to
  - state[from] >= amt
postconditions:
  - sum(result.values()) == sum(state.values())
invariants:
  - type: idempotent
  - type: conservation
faultModel:
  delivery: at_least_once
  reorder: true
  crash_restart: true
bounds:
  accts: 3
  retries: 2
```

## Architecture

Guardrails: Atomic uses **CEGIS (Counter-Example Guided Inductive Synthesis)** with TLA+ model checking:

1. Parse YAML specification
2. Generate initial TypeScript code with LLM
3. Translate specification to TLA+ formal model
4. Run TLC model checker in Docker
5. If violations found, extract counterexample
6. Use counterexample to repair code with LLM
7. Repeat until verified or max iterations reached

## License

MIT
