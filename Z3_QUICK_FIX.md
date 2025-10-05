# Z3 WASM Quick Fix Guide

If you're seeing this error:
```
Z3 execution failed: Aborted(Error: ENOENT: no such file or directory, open '.next/server/vendor-chunks/z3-built.wasm')
```

## Solution A: Automatic (Recommended)

The dev server now automatically watches and copies Z3 files. Just run:

```bash
pnpm dev
```

Wait about 5-10 seconds for Next.js to compile, then try your verification again.

---

## Solution B: Manual Fix (If automatic doesn't work)

### Step 1: Start the dev server
```bash
pnpm dev
```

### Step 2: In a NEW terminal, run the fix script
```bash
cd /Users/smyansengupta/guardrails-atomic-z3
./scripts/fix-z3-runtime.sh
```

### Step 3: Refresh and retry
Refresh your browser or just retry the verification.

---

## Solution C: Quick One-Liner

In a separate terminal while the dev server is running:

```bash
cd /Users/smyansengupta/guardrails-atomic-z3 && sleep 5 && node scripts/copy-z3-wasm.js
```

---

## Why This Happens

Next.js creates the `.next/server/vendor-chunks/` directory during compilation, but z3-solver needs its WASM files there. Our scripts automatically copy the files, but there's a timing issue during the first compilation.

---

## Permanent Solution

The watch script (`scripts/watch-and-copy-z3.js`) runs automatically with `pnpm dev` and should handle this automatically. If it's not working, check:

1. **Check if watcher is running:**
   ```bash
   ps aux | grep watch-and-copy-z3
   ```

2. **Check if files are in place:**
   ```bash
   ls -la .next/server/vendor-chunks/ | grep z3
   ```

3. **Manually trigger copy:**
   ```bash
   node scripts/copy-z3-wasm.js
   ```

---

## Alternative: Use Z3 API Endpoint

If the WASM issue persists, you can use the dedicated Z3 endpoint:

Change your frontend code from:
```typescript
const response = await fetch('/api/verify-stream', ...)
```

To:
```typescript
const response = await fetch('/api/verify-z3', ...)
```

This endpoint is specifically configured for Z3 and may have better WASM handling.

---

## Testing

After applying the fix, test with:

```bash
curl -X POST http://localhost:3001/api/verify-stream \
  -H "Content-Type: application/json" \
  -d '{"spec": "name: test_handler\nfunction_signature:\n  params:\n    - name: x\n      type: int\n  return_type: int\npreconditions: []\npostconditions: []\ninvariants: []\nfault_model:\n  delivery: exactly_once\n  reorder: false\n  crash_restart: false\nbounds:\n  max_value: 10"}'
```

You should see log output showing Z3 initialization and verification.

---

## Still Not Working?

1. Clean everything and restart:
   ```bash
   rm -rf .next
   rm -rf public/z3
   pnpm install
   pnpm dev
   ```

2. Wait 10 seconds for full compilation

3. Run the fix script in another terminal:
   ```bash
   ./scripts/fix-z3-runtime.sh
   ```

4. If still failing, check the logs:
   ```bash
   tail -f logs/app.log | grep Z3
   ```

---

**Quick Summary:**
1. Start `pnpm dev`
2. Wait 10 seconds
3. Run `./scripts/fix-z3-runtime.sh` in another terminal
4. Retry verification

The watcher should then keep files in sync for subsequent hot reloads.

