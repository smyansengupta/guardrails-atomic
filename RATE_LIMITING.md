# Rate Limiting Implementation ✅

## Overview

Implemented comprehensive rate limiting for the `/api/generate-spec` endpoint to prevent spam and abuse. Users are limited to **1 request per minute** with a countdown timer.

---

## Backend Implementation

### Rate Limiter Utility
**File**: `lib/utils/rate-limiter.ts`

**Features**:
- ✅ In-memory storage (simple, fast, no database needed)
- ✅ IP-based tracking
- ✅ Configurable time windows
- ✅ Automatic cleanup of old entries
- ✅ Singleton pattern for shared state

**Configuration**:
```typescript
// 1 request per 60 seconds (1 minute)
export const generateSpecLimiter = new RateLimiter(60000, 1);
```

**How It Works**:
1. Stores timestamps of requests per client IP
2. Checks if request count exceeds limit within time window
3. Returns remaining time if limit exceeded
4. Auto-cleans old entries every 5 minutes

---

### API Endpoint Integration
**File**: `app/api/generate-spec/route.ts`

**Rate Limit Response** (HTTP 429):
```json
{
  "error": "Rate limit exceeded. Please wait before generating another spec.",
  "remainingSeconds": 45,
  "resetAt": "2025-10-04T16:30:00.000Z"
}
```

**Response Headers**:
```
HTTP/1.1 429 Too Many Requests
Retry-After: 45
X-RateLimit-Limit: 1
X-RateLimit-Remaining: 0
X-RateLimit-Reset: 2025-10-04T16:30:00.000Z
```

**Success Response Headers**:
```
X-RateLimit-Limit: 1
X-RateLimit-Remaining: 0
```

---

## Frontend Implementation

### React Hook: `useGenerateSpec`
**File**: `hooks/useGenerateSpec.ts`

**Features**:
- ✅ Automatic countdown timer
- ✅ Loading states
- ✅ Error handling
- ✅ Success/error callbacks
- ✅ Prevents spam clicking

**Usage Example**:
```typescript
import { useGenerateSpec } from '@/hooks/useGenerateSpec';

function GenerateSpecPage() {
  const {
    generateSpec,
    isLoading,
    error,
    yaml,
    warnings,
    remainingSeconds,
    canGenerate,
  } = useGenerateSpec({
    onSuccess: (yaml, warnings) => {
      console.log('Generated YAML:', yaml);
      if (warnings) console.warn('Warnings:', warnings);
    },
    onError: (error) => {
      console.error('Error:', error);
    },
  });

  return (
    <div>
      <textarea
        placeholder="Describe your handler..."
        onChange={(e) => setDescription(e.target.value)}
      />

      <button
        onClick={() => generateSpec(description)}
        disabled={!canGenerate || isLoading}
      >
        {isLoading
          ? 'Generating...'
          : canGenerate
          ? 'Generate Spec'
          : `Wait ${remainingSeconds}s`}
      </button>

      {error && <div className="error">{error}</div>}
      {yaml && <pre>{yaml}</pre>}
      {warnings && warnings.map(w => <div key={w}>⚠️ {w}</div>)}
    </div>
  );
}
```

---

## Hook API

### `useGenerateSpec(options?)`

**Options**:
```typescript
interface UseGenerateSpecOptions {
  onSuccess?: (yaml: string, warnings?: string[]) => void;
  onError?: (error: string) => void;
}
```

**Returns**:
```typescript
interface UseGenerateSpecReturn {
  generateSpec: (naturalLanguage: string, context?: string) => Promise<void>;
  isLoading: boolean;              // True while API call in progress
  error: string | null;            // Error message if failed
  yaml: string | null;             // Generated YAML spec
  warnings: string[] | null;       // Validation warnings
  remainingSeconds: number;        // Countdown timer (0 when can generate)
  canGenerate: boolean;            // True if allowed to make request
  resetTimer: () => void;          // Manually reset the cooldown
}
```

---

## User Experience Flow

### First Request (Success)
```
User clicks "Generate Spec"
    ↓
API processes request
    ↓
Returns YAML + starts 60s cooldown
    ↓
Button shows "Wait 60s"
    ↓
Timer counts down: 59s, 58s, 57s...
    ↓
At 0s: Button becomes "Generate Spec" again
```

### Spam Prevention
```
User clicks "Generate Spec"
    ↓
User quickly clicks again (within 1 minute)
    ↓
Hook prevents request: shows "Wait 45s"
    ↓
API also blocks if hook bypassed
    ↓
Returns 429 with remaining time
    ↓
Timer shows accurate countdown
```

---

## Testing

### Test Rate Limiting

**Test 1: First Request**
```bash
curl -X POST http://localhost:3000/api/generate-spec \
  -H "Content-Type: application/json" \
  -d '{"naturalLanguage": "Create a transfer function"}'

# Expected: 200 OK with YAML
# Headers: X-RateLimit-Remaining: 0
```

**Test 2: Immediate Second Request**
```bash
# Run immediately after test 1
curl -X POST http://localhost:3000/api/generate-spec \
  -H "Content-Type: application/json" \
  -d '{"naturalLanguage": "Create another function"}'

# Expected: 429 Too Many Requests
# Response includes remainingSeconds
```

**Test 3: After Cooldown**
```bash
# Wait 60 seconds, then run
curl -X POST http://localhost:3000/api/generate-spec \
  -H "Content-Type: application/json" \
  -d '{"naturalLanguage": "Create yet another function"}'

# Expected: 200 OK with new YAML
```

---

## Advanced Frontend Example

### Full Component with Timer Display

```typescript
'use client';

import { useState } from 'react';
import { useGenerateSpec } from '@/hooks/useGenerateSpec';
import { Button } from '@/components/ui/button';
import { Textarea } from '@/components/ui/textarea';
import { Alert } from '@/components/ui/alert';

export default function GenerateSpecPage() {
  const [description, setDescription] = useState('');
  const [context, setContext] = useState('');

  const {
    generateSpec,
    isLoading,
    error,
    yaml,
    warnings,
    remainingSeconds,
    canGenerate,
  } = useGenerateSpec();

  const handleGenerate = async () => {
    if (!description.trim()) {
      return;
    }
    await generateSpec(description, context || undefined);
  };

  const formatTime = (seconds: number) => {
    if (seconds >= 60) {
      const mins = Math.floor(seconds / 60);
      const secs = seconds % 60;
      return `${mins}m ${secs}s`;
    }
    return `${seconds}s`;
  };

  return (
    <div className="max-w-4xl mx-auto p-6 space-y-6">
      <h1 className="text-3xl font-bold">Generate Specification</h1>

      <div className="space-y-4">
        <div>
          <label className="block text-sm font-medium mb-2">
            Describe your handler *
          </label>
          <Textarea
            value={description}
            onChange={(e) => setDescription(e.target.value)}
            placeholder="I want to create a function that transfers money between accounts..."
            rows={4}
            disabled={isLoading}
          />
        </div>

        <div>
          <label className="block text-sm font-medium mb-2">
            Additional Context (optional)
          </label>
          <Textarea
            value={context}
            onChange={(e) => setContext(e.target.value)}
            placeholder="This is for a banking system with at-least-once delivery..."
            rows={2}
            disabled={isLoading}
          />
        </div>

        <div className="flex items-center gap-4">
          <Button
            onClick={handleGenerate}
            disabled={!canGenerate || isLoading || !description.trim()}
            size="lg"
          >
            {isLoading
              ? 'Generating...'
              : canGenerate
              ? 'Generate Specification'
              : `Wait ${formatTime(remainingSeconds)}`}
          </Button>

          {!canGenerate && !isLoading && (
            <span className="text-sm text-muted-foreground">
              Rate limited. Next request in {formatTime(remainingSeconds)}.
            </span>
          )}
        </div>
      </div>

      {error && (
        <Alert variant="destructive">
          <strong>Error:</strong> {error}
        </Alert>
      )}

      {warnings && warnings.length > 0 && (
        <Alert>
          <strong>Warnings:</strong>
          <ul className="list-disc list-inside mt-2">
            {warnings.map((warning, i) => (
              <li key={i}>{warning}</li>
            ))}
          </ul>
        </Alert>
      )}

      {yaml && (
        <div>
          <h2 className="text-xl font-semibold mb-2">Generated YAML</h2>
          <pre className="bg-muted p-4 rounded-lg overflow-auto">
            {yaml}
          </pre>
          <div className="mt-4">
            <Button onClick={() => {/* Navigate to verify page */}}>
              Send to Verification
            </Button>
          </div>
        </div>
      )}
    </div>
  );
}
```

---

## Configuration Options

### Adjust Rate Limit

Edit `lib/utils/rate-limiter.ts`:

```typescript
// Change from 1 request per minute to 2 requests per minute
export const generateSpecLimiter = new RateLimiter(60000, 2);

// Change to 1 request per 30 seconds
export const generateSpecLimiter = new RateLimiter(30000, 1);

// Change to 3 requests per 5 minutes
export const generateSpecLimiter = new RateLimiter(5 * 60 * 1000, 3);
```

### Different Limits for Different Endpoints

```typescript
// In rate-limiter.ts
export const generateSpecLimiter = new RateLimiter(60000, 1);
export const verifyLimiter = new RateLimiter(120000, 1); // 1 per 2 minutes
export const validateLimiter = new RateLimiter(10000, 5); // 5 per 10 seconds
```

---

## Benefits

1. **✅ Prevents Spam** - Users can't accidentally spam the API
2. **✅ Reduces Costs** - Less unnecessary OpenRouter API calls
3. **✅ Better UX** - Clear feedback with countdown timer
4. **✅ Fair Usage** - All users get equal access
5. **✅ Server Protection** - Prevents abuse and overload
6. **✅ Clear Communication** - Users know exactly when they can retry

---

## Limitations

### In-Memory Storage
- ⚠️ Rate limit resets if server restarts
- ⚠️ Not shared across multiple server instances
- ⚠️ For production with multiple servers, consider Redis

### Production Recommendations

For production with multiple servers:

```typescript
// Use Redis or similar
import { Redis } from 'ioredis';

class RedisRateLimiter {
  private redis: Redis;

  async check(identifier: string): Promise<RateLimitResult> {
    const key = `ratelimit:${identifier}`;
    const count = await this.redis.incr(key);

    if (count === 1) {
      await this.redis.expire(key, 60); // 60 seconds
    }

    if (count > 1) {
      const ttl = await this.redis.ttl(key);
      return {
        allowed: false,
        remainingMs: ttl * 1000,
      };
    }

    return { allowed: true };
  }
}
```

---

## Error Handling

The hook handles all error cases:

1. **Rate Limited** - Shows countdown timer
2. **Network Error** - Shows error message
3. **Invalid Input** - Shows validation error
4. **Server Error** - Shows generic error
5. **Timeout** - Shows timeout error

All errors are logged and displayed to the user clearly.

---

## Summary

- ✅ **Backend**: Rate limiter with 1 request per minute
- ✅ **Frontend**: React hook with countdown timer
- ✅ **UX**: Clear feedback and disabled states
- ✅ **Testing**: Easy to test with curl
- ✅ **Configurable**: Change limits easily
- ✅ **Type-Safe**: Full TypeScript support

Users can now safely use the generate spec feature without worrying about accidental spam or abuse!

---

*Implemented: 2025-10-04*
*Rate Limit: 1 request per 60 seconds*
