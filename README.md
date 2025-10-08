# Guardrails: Atomic

AI-powered code generation with **formal correctness guarantees** for distributed systems using CEGIS and Z3 SMT solver.

[![TypeScript](https://img.shields.io/badge/TypeScript-100%25-blue)](https://www.typescriptlang.org/)
[![Next.js](https://img.shields.io/badge/Next.js-15-black)](https://nextjs.org/)
[![Z3](https://img.shields.io/badge/Z3-SMT_Solver-green)](https://github.com/Z3Prover/z3)

## What is Guardrails: Atomic?

Guardrails: Atomic automatically generates **formally verified** TypeScript handlers for distributed systems. It uses:

- 🤖 **AI Code Generation**: GPT-4 via OpenRouter
- ✅ **Formal Verification**: Z3 SMT Solver proves correctness
- 🔄 **CEGIS Loop**: Iterative synthesis with counterexample-guided repair
- 🛡️ **Fault Tolerance**: Handles at-least-once delivery, reordering, crashes

### Why?

Writing correct distributed systems code is hard. Common bugs include:
- Double-spending under duplicate message delivery
- Race conditions from message reordering
- Partial state updates after crashes
- Idempotency violations

Guardrails: Atomic **proves your code is correct** before you deploy it.

---

## Quick Start

### Prerequisites

- **Node.js 20+**
- **pnpm** (package manager)
- **OpenRouter API Key**: [openrouter.ai/keys](https://openrouter.ai/keys)

Optional (for production):
- **Clerk account**: [clerk.com](https://clerk.com)
- **MongoDB Atlas**: [mongodb.com/atlas](https://www.mongodb.com/atlas)

### Installation

```bash
# 1. Clone the repository
git clone https://github.com/yourusername/guardrails-atomic.git
cd guardrails-atomic

# 2. Install dependencies
pnpm install

# 3. Set up environment variables
cp .env.local.example .env.local
# Edit .env.local and add your OPENROUTER_API_KEY

# 4. Run development server
pnpm dev
```

Open [http://localhost:3000](http://localhost:3000)

---

## How It Works

### The CEGIS Loop

```
User YAML Spec
      ↓
┌─────────────────────────────────┐
│  CEGIS Loop (max 8 iterations) │
│                                 │
│  1. LLM generates TypeScript    │
│  2. Translate to Z3 constraints │
│  3. Run Z3 solver               │
│  4. If 'sat' (bug found):       │
│     → Extract counterexample    │
│     → Repair code with LLM      │
│  5. If 'unsat' (verified): ✅   │
└─────────────────────────────────┘
      ↓
Formally Verified Code
```

### Example Workflow

1. **Describe** your distributed system handler in YAML:
   ```yaml
   name: transfer_atomic
   invariants:
     - type: idempotent        # No double-spending
     - type: conservation      # Balance preserved
   faultModel:
     delivery: at_least_once   # Messages may duplicate
   ```

2. **Generate** code with AI

3. **Verify** with Z3:
   - ❌ If bugs found → Z3 provides counterexample → LLM repairs
   - ✅ If verified → You get proven-correct code!

---

## Example

### Input: YAML Specification

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

### Output: Verified TypeScript Code

```typescript
function transfer_atomic(
  state: Map<string, number>,
  from: string,
  to: string,
  amt: number,
  req_id: string,
  processedRequests: Set<string>
): Map<string, number> {
  // Idempotency check
  if (processedRequests.has(req_id)) {
    return state; // Already processed, no-op
  }

  // Precondition checks
  if (amt < 0 || from === to || (state.get(from) ?? 0) < amt) {
    throw new Error('Precondition violated');
  }

  // Atomic state update
  const newState = new Map(state);
  newState.set(from, (newState.get(from) ?? 0) - amt);
  newState.set(to, (newState.get(to) ?? 0) + amt);

  // Mark as processed
  processedRequests.add(req_id);

  return newState;
}
```

**Guarantees:**
✅ Idempotent - duplicate messages have no effect
✅ Conservation - total balance preserved
✅ Atomic - no partial updates
✅ **Formally verified by Z3 SMT solver**

---

## Documentation

- 📐 **[Architecture Guide](docs/ARCHITECTURE.md)** - System design, CEGIS loop, Z3 integration
- 🛠️ **[Development Guide](docs/DEVELOPMENT.md)** - Setup, testing, debugging
- 🤖 **[CLAUDE.md](CLAUDE.md)** - AI assistant guide (for Claude Code)

---

## Tech Stack

| Component | Technology |
|-----------|-----------|
| **Frontend/Backend** | Next.js 15, React 19 |
| **Language** | TypeScript (100%) |
| **Formal Verification** | Z3 SMT Solver |
| **AI Code Generation** | OpenRouter (GPT-4) |
| **Authentication** | Clerk |
| **Database** | MongoDB Atlas |
| **Testing** | Vitest |
| **Styling** | Tailwind CSS |

---

## Project Structure

```
guardrails-atomic/
├── app/                   # Next.js App Router
│   ├── api/               # API routes
│   │   ├── verify/        # Main verification endpoint
│   │   ├── generate-spec/ # NL to YAML generator
│   │   └── ...
│   ├── verify/            # Verification UI
│   └── examples/          # Example specs
│
├── lib/                   # Core logic
│   ├── core/              # CEGIS loop
│   ├── verification/      # Z3 integration
│   └── types/             # TypeScript types
│
├── components/            # React components
├── docs/                  # Documentation
├── tests/                 # Test suite
└── scripts/               # Build scripts
```

---

## Testing

```bash
# Run all tests
pnpm test

# Watch mode
pnpm test --watch

# UI mode
pnpm test:ui
```

---

## Building

```bash
# Development
pnpm dev

# Production build
pnpm build
pnpm start

# Linting
pnpm lint
```

---

## Contributing

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Commit your changes (`git commit -m 'feat: Add amazing feature'`)
4. Push to the branch (`git push origin feature/amazing-feature`)
5. Open a Pull Request

---

## Future Plans

### Planned Features
- 🔑 User-provided API keys (bring your own OpenRouter/OpenAI key)
- 💾 Caching of verified implementations
- 🌍 Multi-language code generation (Python, Go, Rust)
- 🧩 Custom invariants via user-defined predicates
- 🤝 Real-time collaboration

### Research Directions
- Neural-guided synthesis (ML to predict good candidates)
- Compositional verification (verify modules independently)
- Automatic fault model inference from tests

---

## License

MIT

---

## Acknowledgments

- **Z3 Solver**: Microsoft Research
- **OpenRouter**: LLM API aggregation
- **Next.js & Vercel**: Web framework and deployment
- **Clerk**: Authentication
- **MongoDB**: Database

---

**Built during ALIHacks (2025)**
**Modernized and production-ready (2025)**