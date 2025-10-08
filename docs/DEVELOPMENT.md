# Development Guide

## Table of Contents
1. [Getting Started](#getting-started)
2. [Development Workflow](#development-workflow)
3. [Testing](#testing)
4. [Debugging](#debugging)
5. [Common Tasks](#common-tasks)
6. [Troubleshooting](#troubleshooting)

---

## Getting Started

### Prerequisites

- **Node.js**: 20+
- **pnpm**: 10.11.0+ (package manager)
- **OpenRouter API Key**: Get from [openrouter.ai/keys](https://openrouter.ai/keys)
- **Clerk Account** (optional for local dev): Get from [clerk.com](https://clerk.com)
- **MongoDB Atlas** (optional for local dev): Get from [mongodb.com/atlas](https://www.mongodb.com/atlas)

### Installation

1. **Clone the repository**:
   ```bash
   git clone <your-repo-url>
   cd guardrails-atomic
   ```

2. **Install dependencies**:
   ```bash
   pnpm install
   ```

   This will automatically:
   - Install all npm packages
   - Copy Z3 WASM files to `public/z3/` (via postinstall script)

3. **Set up environment variables**:
   ```bash
   cp .env.local.example .env.local
   ```

   Edit `.env.local` and add your keys:
   ```bash
   # Required for verification to work
   OPENROUTER_API_KEY=sk-or-v1-your-key-here

   # Optional for local development
   NEXT_PUBLIC_CLERK_PUBLISHABLE_KEY=pk_test_...
   CLERK_SECRET_KEY=sk_test_...
   MONGODB_URI=mongodb+srv://...
   ```

4. **Run development server**:
   ```bash
   pnpm dev
   ```

   Open [http://localhost:3000](http://localhost:3000)

---

## Development Workflow

### Running the Dev Server

```bash
pnpm dev
```

This starts:
- Next.js dev server on port 3000
- Z3 WASM watcher (copies files on changes)
- Hot reload for code changes

### Building for Production

```bash
pnpm build
```

This:
1. Runs `prebuild` script (copies Z3 WASM files)
2. Builds Next.js app
3. Type-checks all TypeScript files
4. Outputs to `.next/` directory

### Running Production Build

```bash
pnpm build
pnpm start
```

### Linting

```bash
pnpm lint
```

Fix auto-fixable issues:
```bash
pnpm lint --fix
```

---

## Testing

### Run All Tests

```bash
pnpm test
```

### Run Tests in Watch Mode

```bash
pnpm test --watch
```

### Run Tests with UI

```bash
pnpm test:ui
```

Opens Vitest UI at [http://localhost:51204](http://localhost:51204)

### Test Structure

```
tests/
├── unit/                       # Unit tests for individual modules
│   ├── spec-parser.test.ts     # YAML parsing
│   ├── code-generator.test.ts  # LLM code generation
│   ├── z3-generator.test.ts (TODO)
│   └── cegis-loop.test.ts      # CEGIS orchestration
├── integration/                # End-to-end tests
│   └── cegis-loop.test.ts      # Full verification flow
└── fixtures/                   # Test data
    └── specs/                  # Example YAML specs
```

### Writing Tests

```typescript
import { describe, it, expect } from 'vitest';
import { parseSpec } from '@/lib/core/spec-parser';

describe('spec-parser', () => {
  it('should parse valid YAML', () => {
    const yaml = `
name: test_transfer
signature:
  params:
    - name: amt
      type: int
  returnType: void
preconditions:
  - amt >= 0
postconditions: []
invariants: []
faultModel:
  delivery: at_least_once
  reorder: false
  crash_restart: false
bounds:
  accts: 3
  retries: 2
`;
    const spec = parseSpec(yaml);
    expect(spec.name).toBe('test_transfer');
    expect(spec.preconditions).toContain('amt >= 0');
  });
});
```

### Mocking External Services

```typescript
import { vi } from 'vitest';

// Mock OpenRouter API
vi.mock('@/lib/services/openrouter.service', () => ({
  generateWithOpenRouter: vi.fn().mockResolvedValue('function transfer() { ... }'),
}));
```

---

## Debugging

### Debugging the CEGIS Loop

1. **Enable debug logging**:
   ```typescript
   // In lib/utils/logger.ts
   const logLevel = 'debug'; // Change from 'info'
   ```

2. **Check Z3 constraints**:
   - Look for logs: `Generated Z3 constraints:`
   - Copy the SMT-LIB output
   - Validate with online Z3 playground: [rise4fun.com/z3](https://rise4fun.com/z3)

3. **Examine counterexamples**:
   - Check `z3Result.counterExample` in iteration history
   - Look for `violatedConstraint` and `model` fields
   - Use trace to understand what values trigger the bug

### Debugging Z3 Integration

```bash
# Test Z3 directly
pnpm tsx scripts/test-z3.ts
```

If Z3 fails to initialize:
1. Check `public/z3/*.wasm` files exist
2. Run `pnpm tsx scripts/copy-z3-wasm.ts`
3. Verify `z3-solver` package is installed

### Debugging OpenRouter API

```bash
# Test OpenRouter connection
curl https://openrouter.ai/api/v1/models \
  -H "Authorization: Bearer $OPENROUTER_API_KEY"
```

If API calls fail:
1. Check API key is valid
2. Verify you have credits: [openrouter.ai/credits](https://openrouter.ai/credits)
3. Check rate limits in response headers

### VS Code Debugging

Create `.vscode/launch.json`:
```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "name": "Next.js: debug server-side",
      "type": "node-terminal",
      "request": "launch",
      "command": "pnpm dev"
    },
    {
      "name": "Next.js: debug full stack",
      "type": "node-terminal",
      "request": "launch",
      "command": "pnpm dev",
      "serverReadyAction": {
        "pattern": "started server on .+, url: (https?://.+)",
        "uriFormat": "%s",
        "action": "debugWithChrome"
      }
    }
  ]
}
```

---

## Common Tasks

### Adding a New Invariant Type

1. **Update type definition** (`lib/types/specification.ts`):
   ```typescript
   export const InvariantTypeSchema = z.enum([
     'idempotent',
     'no_double_spend',
     'atomic_no_partial_commit',
     'conservation',
     'my_new_invariant', // Add here
   ]);
   ```

2. **Implement Z3 constraint** (`lib/verification/z3-generator.ts`):
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

3. **Add test**:
   ```typescript
   it('should verify my_new_invariant', async () => {
     const spec = parseSpec(yamlWithMyInvariant);
     const result = await runCEGISLoop(spec, 5);
     expect(result.success).toBe(true);
   });
   ```

4. **Update prompt** (`templates/prompts/code-generation.txt`):
   Add description of the new invariant for LLM context.

### Adding a New API Endpoint

1. **Create route file**:
   ```bash
   mkdir -p app/api/my-endpoint
   touch app/api/my-endpoint/route.ts
   ```

2. **Implement handler**:
   ```typescript
   import { NextRequest, NextResponse } from 'next/server';
   import { currentUser } from '@clerk/nextjs/server';

   export async function POST(request: NextRequest) {
     const user = await currentUser();

     if (!user) {
       return NextResponse.json(
         { error: 'Unauthorized' },
         { status: 401 }
       );
     }

     const body = await request.json();

     // ... your logic

     return NextResponse.json({ success: true, data: ... });
   }
   ```

3. **Add types** (`lib/types/api.ts`):
   ```typescript
   export interface MyEndpointRequest {
     field: string;
   }

   export interface MyEndpointResponse {
     success: boolean;
     data?: any;
     error?: string;
   }
   ```

### Modifying the CEGIS Loop

See `lib/core/cegis-loop.ts` for the main orchestration logic.

Key extension points:
- **Code generation**: `lib/core/code-generator.ts`
- **Z3 constraint generation**: `lib/verification/z3-generator.ts`
- **Z3 execution**: `lib/verification/z3-runner.ts`

---

## Troubleshooting

### Build Fails with TypeScript Errors

```bash
# Clear Next.js cache
rm -rf .next

# Reinstall dependencies
rm -rf node_modules
pnpm install

# Rebuild
pnpm build
```

### Z3 WASM Files Not Found

```bash
# Manually copy Z3 files
pnpm tsx scripts/copy-z3-wasm.ts

# Verify files exist
ls -la public/z3/
# Should see: browser.js, node.js, z3-built.js, z3-built.wasm
```

### Tests Fail with "Module not found"

Check `vitest.config.ts` has correct path aliases:
```typescript
resolve: {
  alias: {
    '@': path.resolve(__dirname, './'),
  },
},
```

### MongoDB Connection Fails

1. Check MongoDB URI is correct
2. Verify IP whitelist includes your IP (or use `0.0.0.0/0` for development)
3. Test connection:
   ```bash
   mongosh "mongodb+srv://your-connection-string"
   ```

### OpenRouter API Rate Limits

OpenRouter has rate limits per model. If you hit limits:
1. Add exponential backoff in `openrouter.service.ts`
2. Switch to a different model (e.g., `openai/gpt-3.5-turbo`)
3. Check your usage: [openrouter.ai/activity](https://openrouter.ai/activity)

### Verification Never Succeeds

If CEGIS loop always hits max iterations:

1. **Check Z3 constraints**:
   - Enable debug logging
   - Look for "Could not translate formula" warnings
   - Verify all preconditions/postconditions are being translated

2. **Simplify the spec**:
   - Reduce `bounds.accts` from 5 to 3
   - Remove complex preconditions
   - Test with a known-good example

3. **Check LLM prompts**:
   - Review `templates/prompts/code-generation.txt`
   - Ensure prompts provide enough context
   - Try a more capable model (GPT-4 instead of GPT-3.5)

---

## Performance Tips

### Speed Up Development

1. **Use `.env.local` for local dev**:
   ```bash
   # Skip Clerk auth in local dev
   NEXT_PUBLIC_CLERK_PUBLISHABLE_KEY=
   CLERK_SECRET_KEY=
   ```

2. **Run tests in parallel**:
   ```bash
   pnpm test --reporter=verbose --pool=threads --poolOptions.threads.maxThreads=4
   ```

3. **Use build cache**:
   ```bash
   # Next.js caches builds in .next
   # Don't delete unless necessary
   ```

### Optimize Verification Speed

1. **Reduce bounds**:
   ```yaml
   bounds:
     accts: 2  # Instead of 5
     retries: 1  # Instead of 3
   ```

2. **Use simpler models**:
   - GPT-3.5-Turbo is 10x faster than GPT-4
   - Trade-off: May need more iterations

3. **Cache verified specs** (TODO):
   Store hash of spec → verified code in MongoDB

---

## Coding Standards

### TypeScript

- **Strict mode**: Always enabled
- **No `any`**: Use `unknown` and type guards
- **Explicit return types**: For public functions
- **JSDoc comments**: For exported functions

### File Naming

- **Components**: PascalCase (`SpecEditor.tsx`)
- **Utilities**: kebab-case (`rate-limiter.ts`)
- **Types**: kebab-case (`verification.ts`)
- **API routes**: kebab-case (`generate-spec/route.ts`)

### Import Order

```typescript
// 1. External packages
import { useState } from 'react';
import { z } from 'zod';

// 2. Internal modules (absolute imports)
import { parseSpec } from '@/lib/core/spec-parser';
import type { Specification } from '@/lib/types/specification';

// 3. Relative imports
import { MyComponent } from './MyComponent';

// 4. Styles
import './styles.css';
```

---

## Git Workflow

### Commit Messages

Follow conventional commits:
```
feat: Add support for custom invariants
fix: Resolve Z3 formula translation for dynamic arrays
docs: Update architecture guide
refactor: Simplify CEGIS loop error handling
test: Add integration tests for verification flow
```

### Branch Naming

```
feature/custom-invariants
fix/z3-dynamic-arrays
docs/update-readme
refactor/simplify-cegis-loop
```

---

*Last Updated: 2025-10-08 (Phase 1 Modernization)*
