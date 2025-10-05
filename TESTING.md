# Testing Guide

Comprehensive unit tests for Guardrails: Atomic backend functionality.

---

## Overview

This project uses **Vitest** for unit testing with comprehensive coverage of non-API-dependent code. Tests follow TDD (Test-Driven Development) principles.

---

## Test Structure

```
tests/
├── unit/                           # Unit tests (no external dependencies)
│   ├── spec-parser.test.ts        # YAML parsing and validation ✅
│   ├── rate-limiter.test.ts       # Rate limiting logic ✅
│   ├── errors.test.ts             # Error classes ✅
│   ├── tla-generator.test.ts      # TLA+ generation (placeholder)
│   └── counterexample-parser.test.ts # TLC output parsing (placeholder)
│
├── integration/                    # Integration tests (with mocked APIs)
│   └── (future tests)
│
└── fixtures/                       # Test data
    └── example-specs/              # Sample YAML specifications
```

---

## Running Tests

### Run All Tests
```bash
pnpm test
```

### Run Specific Test File
```bash
pnpm test spec-parser
```

### Run with UI
```bash
pnpm test:ui
```

### Watch Mode
```bash
pnpm test --watch
```

### Coverage Report
```bash
pnpm test --coverage
```

---

## Test Coverage

### ✅ Fully Tested Modules

#### 1. **spec-parser.ts** (23 tests)
- ✅ Valid YAML parsing
- ✅ Invalid YAML handling
- ✅ Schema validation
- ✅ Edge cases (empty arrays, complex types, whitespace)

**Coverage**: ~100%

#### 2. **rate-limiter.ts** (25+ tests)
- ✅ Basic rate limiting (allow/block)
- ✅ Multiple request limits
- ✅ Custom time windows
- ✅ Remaining time calculation
- ✅ Client isolation
- ✅ Cleanup functionality
- ✅ IP extraction from headers

**Coverage**: ~100%

#### 3. **errors.ts** (20+ tests)
- ✅ All error class constructors
- ✅ Error inheritance
- ✅ Type checking with instanceof
- ✅ Error serialization
- ✅ Edge cases (unicode, long messages, empty)

**Coverage**: 100%

---

## Test Examples

### Spec Parser Tests

```typescript
it('should parse valid transfer spec', () => {
  const yaml = `
name: transfer_atomic
signature:
  params:
    - name: from
      type: Acct
  returnType: boolean
preconditions: []
postconditions: []
invariants:
  - type: idempotent
faultModel:
  delivery: at_least_once
  reorder: true
  crash_restart: false
bounds:
  accts: 3
`;

  const spec = parseSpec(yaml);

  expect(spec.name).toBe('transfer_atomic');
  expect(spec.invariants[0].type).toBe('idempotent');
});
```

### Rate Limiter Tests

```typescript
it('should block second request within window', () => {
  const limiter = new RateLimiter(60000, 1);

  limiter.check('client1'); // First request

  vi.advanceTimersByTime(30000); // 30 seconds later

  const result = limiter.check('client1'); // Second request

  expect(result.allowed).toBe(false);
  expect(result.remainingMs).toBeGreaterThan(0);
});
```

### Error Class Tests

```typescript
it('should create SpecificationError with correct properties', () => {
  const error = new SpecificationError('Invalid YAML');

  expect(error).toBeInstanceOf(Error);
  expect(error.name).toBe('SpecificationError');
  expect(error.message).toBe('Invalid YAML');
  expect(error.stack).toBeDefined();
});
```

---

## Writing New Tests

### Test File Template

```typescript
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { YourFunction } from '@/lib/path/to/module';

describe('YourModule', () => {
  describe('Feature group', () => {
    it('should do something specific', () => {
      // Arrange
      const input = 'test input';

      // Act
      const result = YourFunction(input);

      // Assert
      expect(result).toBe('expected output');
    });
  });

  describe('Error handling', () => {
    it('should throw on invalid input', () => {
      expect(() => YourFunction(null)).toThrow();
    });
  });

  describe('Edge cases', () => {
    it('should handle empty input', () => {
      const result = YourFunction('');
      expect(result).toBeDefined();
    });
  });
});
```

---

## Testing Principles

### 1. **Arrange-Act-Assert (AAA)**
```typescript
it('should calculate correctly', () => {
  // Arrange: Set up test data
  const a = 5;
  const b = 3;

  // Act: Execute the function
  const result = add(a, b);

  // Assert: Verify the result
  expect(result).toBe(8);
});
```

### 2. **Test One Thing Per Test**
✅ Good:
```typescript
it('should parse name field', () => {
  const spec = parseSpec(validYaml);
  expect(spec.name).toBe('transfer_atomic');
});

it('should parse signature params', () => {
  const spec = parseSpec(validYaml);
  expect(spec.signature.params).toHaveLength(5);
});
```

❌ Bad:
```typescript
it('should parse everything', () => {
  const spec = parseSpec(validYaml);
  expect(spec.name).toBe('transfer_atomic');
  expect(spec.signature.params).toHaveLength(5);
  expect(spec.invariants).toBeDefined();
  // Too many assertions...
});
```

### 3. **Descriptive Test Names**
✅ Good:
```typescript
it('should throw SpecificationError on invalid YAML syntax')
it('should allow request after time window expires')
it('should extract IP from x-forwarded-for header')
```

❌ Bad:
```typescript
it('works')
it('test 1')
it('error case')
```

### 4. **Test Edge Cases**
Always test:
- Empty inputs
- Null/undefined
- Very large inputs
- Invalid types
- Boundary conditions

---

## Mocking API Calls (Future)

For functions that call APIs (OpenRouter, TLC Docker), we'll use Vitest mocks:

### Example: Mocking OpenRouter

```typescript
import { vi } from 'vitest';
import { generateWithOpenRouter } from '@/lib/services/openrouter.service';

// Mock the module
vi.mock('@/lib/services/openrouter.service', () => ({
  generateWithOpenRouter: vi.fn(),
}));

it('should generate YAML from natural language', async () => {
  // Setup mock response
  vi.mocked(generateWithOpenRouter).mockResolvedValue('```yaml\nname: test\n```');

  const result = await generateYAMLFromNL('Create a function');

  expect(result.yaml).toContain('name: test');
  expect(generateWithOpenRouter).toHaveBeenCalledOnce();
});
```

---

## Test Data Fixtures

### Creating Test Fixtures

```typescript
// tests/fixtures/specs.ts
export const validTransferSpec = `
name: transfer_atomic
signature:
  params:
    - name: from
      type: Acct
  returnType: boolean
preconditions: []
postconditions: []
invariants:
  - type: idempotent
faultModel:
  delivery: at_least_once
  reorder: true
  crash_restart: false
bounds:
  accts: 3
`;

export const invalidSpec = `
name: invalid
# Missing required fields
`;
```

### Using Fixtures

```typescript
import { validTransferSpec, invalidSpec } from '@/tests/fixtures/specs';

it('should parse valid spec', () => {
  const spec = parseSpec(validTransferSpec);
  expect(spec.name).toBe('transfer_atomic');
});

it('should reject invalid spec', () => {
  expect(() => parseSpec(invalidSpec)).toThrow();
});
```

---

## Continuous Integration

### GitHub Actions (Example)

```yaml
name: Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest

    steps:
      - uses: actions/checkout@v3
      - uses: pnpm/action-setup@v2
      - uses: actions/setup-node@v3
        with:
          node-version: '18'
          cache: 'pnpm'

      - run: pnpm install
      - run: pnpm test
      - run: pnpm test --coverage

      - name: Upload coverage
        uses: codecov/codecov-action@v3
```

---

## Test Utilities

### Time Manipulation (Vitest)

```typescript
import { vi } from 'vitest';

beforeEach(() => {
  vi.useFakeTimers();
});

afterEach(() => {
  vi.restoreAllMocks();
});

it('should work with time', () => {
  const start = Date.now();

  vi.advanceTimersByTime(60000); // Fast-forward 60 seconds

  const end = Date.now();

  expect(end - start).toBe(60000);
});
```

### Custom Matchers

```typescript
expect.extend({
  toBeValidSpec(received) {
    const pass = received.name && received.signature && received.faultModel;
    return {
      pass,
      message: () => `Expected ${received} to be a valid specification`,
    };
  },
});

it('should return valid spec', () => {
  const spec = parseSpec(yaml);
  expect(spec).toBeValidSpec();
});
```

---

## Coverage Goals

| Module | Current | Goal |
|--------|---------|------|
| spec-parser.ts | 100% | 100% ✅ |
| rate-limiter.ts | 100% | 100% ✅ |
| errors.ts | 100% | 100% ✅ |
| nl-to-yaml-generator.ts | 0% | 80% (with mocks) |
| tla-generator.ts | 0% | 80% |
| tlc-runner.ts | 0% | 60% (with mocks) |
| code-generator.ts | 0% | 80% (with mocks) |

---

## Testing Checklist

Before committing code, ensure:

- [ ] All new functions have unit tests
- [ ] Edge cases are covered
- [ ] Error paths are tested
- [ ] Tests are descriptive and focused
- [ ] No API calls in unit tests (mock them)
- [ ] Tests run in isolation (no shared state)
- [ ] `pnpm test` passes locally

---

## Debugging Tests

### Run Single Test
```bash
pnpm test -t "should parse valid transfer spec"
```

### Debug with VS Code
Add to `.vscode/launch.json`:
```json
{
  "type": "node",
  "request": "launch",
  "name": "Debug Vitest",
  "runtimeExecutable": "pnpm",
  "runtimeArgs": ["test", "--run", "--no-coverage"],
  "console": "integratedTerminal"
}
```

### Print Debug Info
```typescript
it('should work', () => {
  const result = myFunction();
  console.log('Result:', result); // Shows in test output
  expect(result).toBe(expected);
});
```

---

## Common Test Patterns

### Testing Async Functions
```typescript
it('should resolve successfully', async () => {
  const result = await asyncFunction();
  expect(result).toBe('success');
});

it('should reject with error', async () => {
  await expect(asyncFunction()).rejects.toThrow('Error message');
});
```

### Testing Promises
```typescript
it('should return promise', () => {
  return asyncFunction().then(result => {
    expect(result).toBe('value');
  });
});
```

### Testing Error Messages
```typescript
it('should throw with specific message', () => {
  expect(() => throwError()).toThrow('Specific error message');
  expect(() => throwError()).toThrow(/regex pattern/);
});
```

### Testing Object Properties
```typescript
it('should have correct structure', () => {
  const obj = createObject();

  expect(obj).toHaveProperty('name');
  expect(obj).toHaveProperty('age', 25);
  expect(obj).toMatchObject({ name: 'test', age: 25 });
});
```

---

## Resources

- [Vitest Documentation](https://vitest.dev/)
- [Testing Best Practices](https://testingjavascript.com/)
- [TDD Guide](https://martinfowler.com/bliki/TestDrivenDevelopment.html)

---

## Summary

- ✅ **23 tests** for spec-parser
- ✅ **25+ tests** for rate-limiter
- ✅ **20+ tests** for error classes
- ✅ **100% coverage** on tested modules
- ✅ **Fast execution** (<1s for all tests)
- ✅ **Isolated tests** (no external dependencies)

Run `pnpm test` to verify everything works!

---

*Last Updated: 2025-10-04*
*Test Framework: Vitest 1.x*
