# Work Plan: Full Working CEGIS Loop

**Goal**: Get the complete CEGIS verification pipeline working end-to-end with real-time progress updates

**Estimated Time**: 3-4 hours (assuming OpenRouter API key available)

---

## Phase 1: Environment Setup & Validation (15 minutes)

### Task 1.1: Set OpenRouter API Key
**File**: `.env.local`
**Priority**: 🔴 CRITICAL

```bash
# Add to .env.local (create if doesn't exist)
OPENROUTER_API_KEY=sk-or-v1-xxxxx...
```

**Verification**:
```bash
# Check if key is loaded
grep OPENROUTER_API_KEY .env.local

# Restart dev server
pnpm dev
```

**Acceptance Criteria**:
- ✅ `.env.local` contains `OPENROUTER_API_KEY`
- ✅ Dev server loads without errors
- ✅ `/api/generate-code` endpoint can make LLM calls

---

### Task 1.2: Verify Docker TLC Setup
**Priority**: 🔴 CRITICAL

```bash
# Check Docker daemon
docker ps

# Check TLC image
docker images | grep guardrails-tlc

# Test TLC execution manually
cd docker
docker run --rm -v $(pwd)/tlc:/workspace guardrails-tlc --help
```

**Acceptance Criteria**:
- ✅ Docker daemon running
- ✅ `guardrails-tlc` image exists
- ✅ TLC can be invoked via Docker

---

## Phase 2: Component Testing (1-1.5 hours)

### Task 2.1: Test Code Generator
**File**: `lib/core/code-generator.ts`
**Priority**: 🟡 HIGH

**Manual Test**:
```bash
# Create test script: scripts/test-code-gen.ts
import { parseSpec } from '@/lib/core/spec-parser';
import { generateCode } from '@/lib/core/code-generator';
import { readFile } from 'fs/promises';

const specYaml = await readFile('templates/specs/transfer.yaml', 'utf-8');
const spec = parseSpec(specYaml);
const code = await generateCode(spec);

console.log('Generated Code:');
console.log(code);
```

**Run**:
```bash
pnpm tsx scripts/test-code-gen.ts
```

**Acceptance Criteria**:
- ✅ Code generator calls OpenRouter successfully
- ✅ Returns valid TypeScript code
- ✅ Code includes idempotency checks (if spec requires)
- ✅ Code handles parameters correctly

**If Fails**:
- Check `OPENROUTER_API_KEY` is set
- Verify `templates/prompts/code-generation.txt` exists
- Check OpenRouter API rate limits
- Inspect LLM response for errors

---

### Task 2.2: Test TLA+ Generator
**File**: `lib/verification/tla-generator.ts`
**Priority**: 🔴 CRITICAL

**Manual Test**:
```bash
# Create test script: scripts/test-tla-gen.ts
import { parseSpec } from '@/lib/core/spec-parser';
import { generateTLAModule, tlaModuleToString, generateTLCConfig } from '@/lib/verification/tla-generator';
import { readFile, writeFile } from 'fs/promises';

const specYaml = await readFile('templates/specs/transfer.yaml', 'utf-8');
const spec = parseSpec(specYaml);

console.log('Generating TLA+ module...');
const module = await generateTLAModule(spec);
const tlaString = tlaModuleToString(module);
const config = await generateTLCConfig(spec);

console.log('TLA+ Module:');
console.log(tlaString);
console.log('\nTLC Config:');
console.log(config);

// Save for manual inspection
await writeFile('output/Transfer.tla', tlaString);
await writeFile('output/Transfer.cfg', config);
```

**Run**:
```bash
mkdir -p output
pnpm tsx scripts/test-tla-gen.ts
```

**Acceptance Criteria**:
- ✅ TLA+ generator calls OpenRouter successfully
- ✅ Returns valid JSON response
- ✅ Zod schema validation passes
- ✅ Generated TLA+ has correct structure:
  - `MODULE Transfer`
  - `EXTENDS` clause (if needed)
  - `CONSTANTS` declaration
  - `VARIABLES` declaration
  - `Init` predicate
  - Actions (Transfer, DuplicateTransfer, etc.)
  - Invariants (Idempotent, TypeOK, etc.)
  - `Next` relation
- ✅ TLC config has correct structure:
  - `SPECIFICATION Spec`
  - `INVARIANTS` list
  - `CONSTANTS` assignments

**If Fails**:
- **LLM returns invalid JSON**: Fix `templates/prompts/tla-generation.txt` to be more explicit
- **Zod validation fails**: Inspect LLM response, adjust schema or prompt
- **TLA+ syntax errors**: Manually test with TLC (see Task 2.3)

**Common Issues & Fixes**:

| Issue | Fix |
|-------|-----|
| LLM doesn't return JSON | Add "You MUST return valid JSON in a ```json code block" to prompt |
| Missing `EXTENDS` clause | Add example to prompt showing `EXTENDS Naturals, Sequences` |
| Invalid action syntax | Provide template in prompt: `Action(param) == /\ guard /\ update' = ...` |
| Config missing CONSTANTS | Ensure prompt asks for `CONSTANTS Acct <- {"a1", "a2"}` format |

---

### Task 2.3: Test TLC Execution with Generated TLA+
**File**: `lib/verification/tlc-runner.ts`
**Priority**: 🔴 CRITICAL

**Manual Test**:
```bash
# Use output from Task 2.2
cd output

# Run TLC manually
docker run --rm -v $(pwd):/workspace guardrails-tlc Transfer.tla

# Expected output:
# - "TLC2 Version ..."
# - "Computing initial states..."
# - "Checking X states generated, Y distinct states found"
# - Either "Model checking completed. No error has been found."
#   OR "Error: Invariant X is violated."
```

**Acceptance Criteria**:
- ✅ TLC accepts the generated TLA+ (no syntax errors)
- ✅ TLC runs without crashing
- ✅ TLC output is parseable
- ✅ If violations exist, they are correctly identified

**If Fails**:
- **Syntax error**: TLA+ generator prompt needs refinement
- **Semantic error**: Check invariant definitions, action guards
- **TLC crash**: Check TLA+ module structure, missing `Next` relation

**Common TLA+ Syntax Errors**:

| Error | Cause | Fix |
|-------|-------|-----|
| `Unexpected token` | Missing `/\` or `\/` operators | Ensure all actions use `/\` for conjunction |
| `Unknown operator` | Typo in `EXTENDS` clause | Add `EXTENDS Naturals, Sequences, FiniteSets` |
| `Variable X not declared` | Typo in variable name | Ensure consistency: `VARIABLES state` → `state'` |
| `Constant X not defined` | Missing in config | Add `CONSTANTS Acct <- {...}` to `.cfg` |

---

### Task 2.4: Test Counterexample Parsing
**File**: `lib/verification/counterexample-parser.ts`
**Priority**: 🟡 HIGH

**Manual Test**:
```bash
# Create a spec that WILL fail (e.g., missing idempotency check)
# Run TLC to get a violation
# Parse the output

# Create test script: scripts/test-counterexample.ts
import { parseCounterExample, generateRepairFeedback } from '@/lib/verification/counterexample-parser';

// Copy real TLC error output from Task 2.3
const tlcOutput = `
Error: Invariant Idempotent is violated.
The behavior up to this point is:
State 1: ...
State 2: ...
`;

const counterExample = parseCounterExample(tlcOutput);
const feedback = generateRepairFeedback(counterExample);

console.log('Counterexample:');
console.log(JSON.stringify(counterExample, null, 2));
console.log('\nRepair Feedback:');
console.log(feedback);
```

**Acceptance Criteria**:
- ✅ Correctly identifies violated invariant
- ✅ Extracts execution trace (state sequence)
- ✅ Generates actionable repair feedback
- ✅ Feedback includes specific suggestions

**If Fails**:
- Update parsing regexes in `counterexample-parser.ts`
- Add more examples to handle different TLC output formats

---

## Phase 3: End-to-End CEGIS Testing (1-1.5 hours)

### Task 3.1: Test Legacy CEGIS Loop (No SSE)
**File**: `lib/core/cegis-loop.ts`
**Endpoint**: `/api/verify`
**Priority**: 🔴 CRITICAL

**Manual Test**:
```bash
# Use the frontend at http://localhost:3000/verify
# OR use curl

curl -X POST http://localhost:3000/api/verify \
  -H "Content-Type: application/json" \
  -d '{
    "spec": "name: transfer_atomic\nsignature:\n  params:\n    - name: from\n      type: Acct\n  ...",
    "maxIterations": 3
  }'
```

**What to Watch**:
1. **Iteration 1**:
   - Code generation succeeds
   - TLA+ generation succeeds
   - TLC runs
   - (May fail with violation)

2. **Iteration 2** (if iteration 1 failed):
   - Repair feedback used
   - Code regenerated with fixes
   - TLA+ regenerated
   - TLC runs again

3. **Success** or **Max Iterations**:
   - Returns `VerificationResult`
   - Includes `proofReport` if successful
   - Includes `iterationHistory` with all attempts

**Acceptance Criteria**:
- ✅ CEGIS loop runs without crashing
- ✅ All phases execute in order
- ✅ Repair mode triggers on failures
- ✅ Returns structured result
- ✅ Logs are clear and informative

**Expected Timeline**:
- Each iteration: 10-30 seconds (depending on LLM speed)
- Total for 3 iterations: 30-90 seconds

**If Fails**:

| Phase | Failure | Fix |
|-------|---------|-----|
| Code Gen | LLM timeout | Increase timeout in `openrouter.service.ts` |
| TLA+ Gen | Invalid JSON | Refine prompt in `tla-generation.txt` |
| TLC Run | Syntax error | Fix TLA+ generator output |
| Repair | No improvement | Improve `code-repair.txt` prompt |

---

### Task 3.2: Test SSE CEGIS Loop
**File**: `lib/core/cegis-loop-stream.ts`
**Endpoint**: `/api/verify-stream`
**Priority**: 🟡 HIGH

**Manual Test (Browser)**:
```javascript
// Open browser console at http://localhost:3000/verify
// Toggle "Real-Time Updates" ON
// Submit a verification request
// Watch the ProgressDisplay component update in real-time
```

**Manual Test (Curl - SSE)**:
```bash
curl -X POST http://localhost:3000/api/verify-stream \
  -H "Content-Type: application/json" \
  -d '{"spec": "...", "maxIterations": 3}' \
  --no-buffer

# Expected output (SSE stream):
data: {"type":"progress","phase":"parsing",...}

data: {"type":"iteration_start","iteration":1,...}

data: {"type":"progress","phase":"generating_code",...}

data: {"type":"code_generated","iteration":1,"codeLength":1245,...}

...
```

**What to Watch**:
1. **Event Stream Opens**:
   - HTTP response is `text/event-stream`
   - Headers include `Cache-Control: no-cache`

2. **Events Emitted in Order**:
   - `progress` (parsing)
   - `iteration_start` (1)
   - `progress` (generating_code)
   - `code_generated` (1)
   - `progress` (generating_tla)
   - `tla_generated` (1)
   - `tlc_start` (1)
   - `progress` (running_tlc)
   - `tlc_complete` (1)
   - `iteration_complete` (1)
   - (Repeat for iteration 2 if failed)
   - `verification_complete`

3. **Frontend Updates**:
   - ProgressDisplay shows current phase
   - Timeline displays all events
   - Progress bar advances
   - Iteration counter updates (e.g., "2/3")

**Acceptance Criteria**:
- ✅ SSE stream opens successfully
- ✅ Events emitted at correct times
- ✅ Event payloads match `VerificationEvent` types
- ✅ Frontend receives and displays events
- ✅ Stream closes after completion
- ✅ Errors propagate correctly

**If Fails**:

| Issue | Fix |
|-------|-----|
| Stream doesn't open | Check SSE headers in `verify-stream/route.ts` |
| Events not emitted | Verify `emitEvent()` calls in `cegis-loop-stream.ts` |
| Frontend doesn't update | Check `useVerificationStream` hook |
| Stream hangs | Add timeout to SSE connection |

---

### Task 3.3: Test Repair Loop (Intentional Failure)
**Priority**: 🟡 HIGH

**Create Failing Spec**:
```yaml
# templates/specs/intentionally-bad.yaml
name: bad_transfer
signature:
  params:
    - name: from
      type: Acct
    - name: to
      type: Acct
    - name: amount
      type: int
  returnType: Map<Acct,int>

preconditions:
  - "from != to"
  - "state[from] >= amount"

postconditions:
  - "state'[from] = state[from] - amount"
  - "state'[to] = state[to] + amount"

invariants:
  - type: idempotent  # This WILL fail if code doesn't check request_id

faultModel:
  delivery: at_least_once  # Duplicates allowed
  reorder: false
  crash_restart: false

bounds:
  accounts: ["a1", "a2"]
  amounts: [1, 5]
  maxRetries: 2
```

**Expected Behavior**:
1. **Iteration 1**: Code doesn't handle duplicates → TLC finds violation
2. **Iteration 2**: Repair feedback added → Code adds `processed` set → TLC passes

**Acceptance Criteria**:
- ✅ Iteration 1 fails with idempotency violation
- ✅ Counterexample extracted correctly
- ✅ Repair feedback includes "add idempotency check"
- ✅ Iteration 2 regenerates code with `processed` set
- ✅ Iteration 2 passes TLC verification
- ✅ Final result includes proof report

---

## Phase 4: Error Handling & Edge Cases (30 minutes)

### Task 4.1: Test Error Scenarios

**Test Cases**:

1. **Invalid YAML**:
   ```bash
   curl -X POST http://localhost:3000/api/verify \
     -H "Content-Type: application/json" \
     -d '{"spec": "invalid: yaml: syntax::"}'

   # Expected: 400 Bad Request with Zod error
   ```

2. **Missing API Key**:
   ```bash
   # Remove OPENROUTER_API_KEY from .env.local
   # Restart server
   # Try verification

   # Expected: 500 with "API key not configured"
   ```

3. **LLM Timeout**:
   ```bash
   # Set very low timeout in openrouter.service.ts
   # Try verification

   # Expected: Error event with "LLM timeout"
   ```

4. **TLC Timeout**:
   ```bash
   # Create spec with huge state space (bounds too large)
   # Try verification

   # Expected: TLC timeout after 60s
   ```

5. **Docker Not Running**:
   ```bash
   # Stop Docker daemon
   # Try verification

   # Expected: Error about Docker connection
   ```

**Acceptance Criteria**:
- ✅ All errors return proper HTTP status codes
- ✅ Error messages are clear and actionable
- ✅ SSE stream emits `error` events (not just crashes)
- ✅ Frontend displays errors beautifully

---

### Task 4.2: Test Graceful Degradation

**Test TLA+ Generator Failure**:
```bash
# Temporarily break tla-generator.ts (e.g., invalid prompt)
# Try /api/verify

# Expected: 501 "TLA+ verification under development" message
```

**Acceptance Criteria**:
- ✅ Falls back to code-only mode
- ✅ Returns generated code without proof report
- ✅ User-friendly error message

---

## Phase 5: Performance & Stability (30 minutes)

### Task 5.1: Test Long-Running Verification

**Create Complex Spec**:
```yaml
# Large state space to force multiple iterations
bounds:
  accounts: ["a1", "a2", "a3", "a4"]  # 4 accounts
  amounts: [1, 2, 3, 5, 10]           # 5 amounts
  maxRetries: 3
```

**Watch For**:
- ✅ SSE stream stays open (no premature close)
- ✅ Memory usage stays stable
- ✅ Logs don't flood console
- ✅ Frontend remains responsive

---

### Task 5.2: Test Concurrent Requests

```bash
# Start 3 verifications simultaneously
curl -X POST http://localhost:3000/api/verify -d '...' &
curl -X POST http://localhost:3000/api/verify -d '...' &
curl -X POST http://localhost:3000/api/verify -d '...' &
```

**Acceptance Criteria**:
- ✅ All requests complete successfully
- ✅ No race conditions
- ✅ OpenRouter rate limits respected
- ✅ Docker containers don't conflict

---

## Phase 6: Documentation & Cleanup (30 minutes)

### Task 6.1: Update README with Setup Instructions

Add to `README.md`:
```markdown
## Quick Start

1. Clone the repository
2. Install dependencies: `pnpm install`
3. Set up environment variables:
   ```bash
   cp .env.example .env.local
   # Add your OpenRouter API key
   OPENROUTER_API_KEY=sk-or-v1-xxxxx
   ```
4. Build TLC Docker image:
   ```bash
   cd docker
   docker build -t guardrails-tlc .
   ```
5. Start dev server: `pnpm dev`
6. Open http://localhost:3000
```

---

### Task 6.2: Create Example Specs

Ensure `templates/specs/` has working examples:
- ✅ `transfer.yaml` - Basic transfer with idempotency
- ✅ `write.yaml` - Simple write operation
- Add `payment.yaml` - Payment with conservation invariant
- Add `reservation.yaml` - Seat reservation with no-double-spend

---

### Task 6.3: Log Cleanup

Review all components for:
- Remove debug `console.log()` statements
- Ensure all errors are logged with `logger.error()`
- Add INFO logs at key milestones
- Add DEBUG logs for troubleshooting

---

## Phase 7: MVP Validation (30 minutes)

### Task 7.1: End-to-End Demo Flow

**Scenario**: User wants to verify a transfer function

1. Navigate to http://localhost:3000
2. Click "Get Started"
3. Go to "Generate Specification" tab
4. Enter: "A transfer function that moves money from one account to another, must be idempotent under duplicate delivery"
5. Click "Generate Spec" → YAML appears
6. Switch to "Verify Code" tab
7. Toggle "Real-Time Updates" ON
8. Click "Verify"
9. **Watch**:
   - Progress indicator shows phases
   - Timeline shows events
   - Iteration counter updates
   - (If fails) Repair feedback shown
   - (If succeeds) Proof report displayed with green checkmarks
10. Download generated code
11. Copy to clipboard
12. Done! 🎉

**Acceptance Criteria**:
- ✅ Entire flow works without errors
- ✅ UI is responsive and beautiful
- ✅ User gets working, verified code
- ✅ Proof report shows all guarantees

---

### Task 7.2: Record Demo Video

```bash
# Record screen for 2-3 minutes showing:
1. Landing page
2. Spec generation from NL
3. Verification with real-time progress
4. Success with proof report
5. Download code
```

---

## Success Criteria

### ✅ Phase 1 Complete When:
- OpenRouter API key is set and working
- Docker TLC is running
- Dev server starts without errors

### ✅ Phase 2 Complete When:
- Code generator produces valid TypeScript
- TLA+ generator produces valid TLA+ (passes TLC syntax check)
- TLC runner executes and parses output correctly
- Counterexample parser extracts violations

### ✅ Phase 3 Complete When:
- Legacy CEGIS loop runs end-to-end
- SSE CEGIS loop emits all events correctly
- Repair loop iterates and eventually succeeds (or max iterations)
- Frontend displays real-time progress

### ✅ Phase 4 Complete When:
- All error scenarios handled gracefully
- Graceful degradation works (code-only mode)
- Error messages are user-friendly

### ✅ Phase 5 Complete When:
- Long-running verifications are stable
- Concurrent requests work correctly
- Performance is acceptable (<2 min for 3 iterations)

### ✅ Phase 6 Complete When:
- README has clear setup instructions
- Example specs are documented
- Logs are clean and informative

### ✅ Phase 7 Complete When:
- End-to-end demo flow works perfectly
- Demo video recorded
- **MVP is ready to ship!** 🚀

---

## Troubleshooting Guide

### Common Issues

| Symptom | Likely Cause | Fix |
|---------|--------------|-----|
| "OpenRouter API error" | Missing/invalid API key | Check `.env.local`, restart server |
| "TLA+ generation failed" | LLM returned invalid JSON | Inspect `tla-generation.txt` prompt |
| "TLC syntax error" | Generated TLA+ is malformed | Refine TLA+ generator prompt |
| "TLC timeout" | State space too large | Reduce bounds in spec |
| "Docker not found" | Docker daemon not running | Start Docker Desktop |
| "SSE stream closes early" | Error not caught | Check error handling in `cegis-loop-stream.ts` |
| "Frontend doesn't update" | SSE not connected | Check browser console for errors |

---

## Time Estimates

| Phase | Optimistic | Realistic | Pessimistic |
|-------|------------|-----------|-------------|
| Phase 1: Setup | 10 min | 15 min | 30 min |
| Phase 2: Component Testing | 45 min | 1.5 hrs | 3 hrs |
| Phase 3: E2E CEGIS | 30 min | 1 hr | 2 hrs |
| Phase 4: Error Handling | 15 min | 30 min | 1 hr |
| Phase 5: Performance | 15 min | 30 min | 1 hr |
| Phase 6: Documentation | 15 min | 30 min | 1 hr |
| Phase 7: MVP Validation | 15 min | 30 min | 1 hr |
| **TOTAL** | **2.5 hrs** | **4.5 hrs** | **9.5 hrs** |

**Recommendation**: Budget 4-5 hours for a thorough, production-ready implementation.

---

## Next Steps After MVP

1. **Add more example specs** (payment, reservation, distributed counter)
2. **Improve TLA+ prompt** with more examples and templates
3. **Add unit tests for TLA+ generator** (with mocked LLM responses)
4. **Implement caching** for verified specs (skip verification if spec unchanged)
5. **Add deployment docs** (Vercel, Docker Compose, env vars)
6. **Create video tutorial** for users
7. **Write blog post** about CEGIS + TLA+ approach
8. **Open source!** 🎉

---

**Last Updated**: 2025-10-05
**Status**: 🟢 Ready to begin
