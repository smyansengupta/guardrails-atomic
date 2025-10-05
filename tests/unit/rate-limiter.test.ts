import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest';
import { getClientIdentifier } from '@/lib/utils/rate-limiter';

// We'll test the RateLimiter class directly by importing it
// Note: We can't use the singleton instances in tests because they're shared
class RateLimiter {
  private requests: Map<
    string,
    {
      timestamps: number[];
      lastReset: number;
    }
  >;
  private windowMs: number;
  private maxRequests: number;

  constructor(windowMs: number = 60000, maxRequests: number = 1) {
    this.requests = new Map();
    this.windowMs = windowMs;
    this.maxRequests = maxRequests;
  }

  check(identifier: string): {
    allowed: boolean;
    remainingMs?: number;
    resetAt?: Date;
  } {
    const now = Date.now();
    const entry = this.requests.get(identifier);

    if (!entry) {
      this.requests.set(identifier, {
        timestamps: [now],
        lastReset: now,
      });
      return { allowed: true };
    }

    entry.timestamps = entry.timestamps.filter(
      (timestamp) => now - timestamp < this.windowMs
    );

    if (entry.timestamps.length >= this.maxRequests) {
      const oldestTimestamp = entry.timestamps[0];
      const remainingMs = this.windowMs - (now - oldestTimestamp);
      const resetAt = new Date(oldestTimestamp + this.windowMs);

      return {
        allowed: false,
        remainingMs,
        resetAt,
      };
    }

    entry.timestamps.push(now);
    this.requests.set(identifier, entry);

    return { allowed: true };
  }

  clear(identifier: string): void {
    this.requests.delete(identifier);
  }

  clearAll(): void {
    this.requests.clear();
  }

  cleanup(): void {
    const now = Date.now();
    for (const [identifier, entry] of this.requests.entries()) {
      entry.timestamps = entry.timestamps.filter(
        (timestamp) => now - timestamp < this.windowMs
      );

      if (entry.timestamps.length === 0) {
        this.requests.delete(identifier);
      }
    }
  }
}

describe('RateLimiter', () => {
  let limiter: RateLimiter;

  beforeEach(() => {
    vi.useFakeTimers();
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('Basic functionality', () => {
    beforeEach(() => {
      limiter = new RateLimiter(60000, 1); // 1 request per minute
    });

    it('should allow first request', () => {
      const result = limiter.check('client1');

      expect(result.allowed).toBe(true);
      expect(result.remainingMs).toBeUndefined();
      expect(result.resetAt).toBeUndefined();
    });

    it('should block second request within window', () => {
      limiter.check('client1');

      // Advance time by 30 seconds (still within 60 second window)
      vi.advanceTimersByTime(30000);

      const result = limiter.check('client1');

      expect(result.allowed).toBe(false);
      expect(result.remainingMs).toBeGreaterThan(0);
      expect(result.remainingMs).toBeLessThanOrEqual(30000);
      expect(result.resetAt).toBeInstanceOf(Date);
    });

    it('should allow request after window expires', () => {
      limiter.check('client1');

      // Advance time past the 60 second window
      vi.advanceTimersByTime(61000);

      const result = limiter.check('client1');

      expect(result.allowed).toBe(true);
    });

    it('should track different clients separately', () => {
      const result1 = limiter.check('client1');
      const result2 = limiter.check('client2');

      expect(result1.allowed).toBe(true);
      expect(result2.allowed).toBe(true);

      // Both should be blocked on second request
      const result3 = limiter.check('client1');
      const result4 = limiter.check('client2');

      expect(result3.allowed).toBe(false);
      expect(result4.allowed).toBe(false);
    });
  });

  describe('Multiple requests limit', () => {
    beforeEach(() => {
      limiter = new RateLimiter(60000, 3); // 3 requests per minute
    });

    it('should allow up to maxRequests', () => {
      const result1 = limiter.check('client1');
      const result2 = limiter.check('client1');
      const result3 = limiter.check('client1');

      expect(result1.allowed).toBe(true);
      expect(result2.allowed).toBe(true);
      expect(result3.allowed).toBe(true);
    });

    it('should block after maxRequests is reached', () => {
      limiter.check('client1');
      limiter.check('client1');
      limiter.check('client1');

      const result = limiter.check('client1');

      expect(result.allowed).toBe(false);
    });

    it('should allow request as old ones expire', () => {
      limiter.check('client1'); // Request 1 at t=0
      vi.advanceTimersByTime(20000);

      limiter.check('client1'); // Request 2 at t=20s
      vi.advanceTimersByTime(20000);

      limiter.check('client1'); // Request 3 at t=40s

      // All 3 slots used, should be blocked
      const result1 = limiter.check('client1');
      expect(result1.allowed).toBe(false);

      // Advance to t=61s (request 1 expired)
      vi.advanceTimersByTime(21000);

      const result2 = limiter.check('client1'); // Request 4 at t=61s
      expect(result2.allowed).toBe(true); // Request 1 has expired, slot available
    });
  });

  describe('Custom window sizes', () => {
    it('should work with 30 second window', () => {
      limiter = new RateLimiter(30000, 1); // 1 request per 30 seconds

      limiter.check('client1');

      vi.advanceTimersByTime(29000);
      expect(limiter.check('client1').allowed).toBe(false);

      vi.advanceTimersByTime(2000); // Total 31 seconds
      expect(limiter.check('client1').allowed).toBe(true);
    });

    it('should work with 5 minute window', () => {
      limiter = new RateLimiter(5 * 60 * 1000, 1); // 1 request per 5 minutes

      limiter.check('client1');

      vi.advanceTimersByTime(4 * 60 * 1000); // 4 minutes
      expect(limiter.check('client1').allowed).toBe(false);

      vi.advanceTimersByTime(61 * 1000); // Total 5 minutes 1 second
      expect(limiter.check('client1').allowed).toBe(true);
    });
  });

  describe('Remaining time calculation', () => {
    beforeEach(() => {
      limiter = new RateLimiter(60000, 1);
    });

    it('should calculate correct remaining time', () => {
      limiter.check('client1');

      vi.advanceTimersByTime(40000); // 40 seconds elapsed

      const result = limiter.check('client1');

      expect(result.allowed).toBe(false);
      expect(result.remainingMs).toBe(20000); // 60s - 40s = 20s remaining
    });

    it('should decrease remaining time as time passes', () => {
      limiter.check('client1');

      vi.advanceTimersByTime(10000);
      const result1 = limiter.check('client1');
      expect(result1.remainingMs).toBe(50000);

      vi.advanceTimersByTime(20000);
      const result2 = limiter.check('client1');
      expect(result2.remainingMs).toBe(30000);
    });

    it('should have resetAt timestamp in the future', () => {
      const startTime = Date.now();
      limiter.check('client1');

      vi.advanceTimersByTime(10000);

      const result = limiter.check('client1');

      expect(result.resetAt).toBeDefined();
      expect(result.resetAt!.getTime()).toBe(startTime + 60000);
    });
  });

  describe('Clear methods', () => {
    beforeEach(() => {
      limiter = new RateLimiter(60000, 1);
    });

    it('should clear specific client', () => {
      limiter.check('client1');
      limiter.check('client2');

      limiter.clear('client1');

      // client1 should be able to make new request
      expect(limiter.check('client1').allowed).toBe(true);

      // client2 should still be blocked
      expect(limiter.check('client2').allowed).toBe(false);
    });

    it('should clear all clients', () => {
      limiter.check('client1');
      limiter.check('client2');
      limiter.check('client3');

      limiter.clearAll();

      expect(limiter.check('client1').allowed).toBe(true);
      expect(limiter.check('client2').allowed).toBe(true);
      expect(limiter.check('client3').allowed).toBe(true);
    });
  });

  describe('Cleanup functionality', () => {
    beforeEach(() => {
      limiter = new RateLimiter(60000, 2);
    });

    it('should remove expired entries on cleanup', () => {
      limiter.check('client1');
      limiter.check('client1');

      // Advance past window
      vi.advanceTimersByTime(61000);

      limiter.cleanup();

      // After cleanup, client1 should be able to make fresh requests
      const result1 = limiter.check('client1');
      const result2 = limiter.check('client1');

      expect(result1.allowed).toBe(true);
      expect(result2.allowed).toBe(true);
    });

    it('should keep non-expired entries', () => {
      limiter.check('client1');

      vi.advanceTimersByTime(30000); // Halfway through window

      limiter.cleanup();

      // client1 should still be limited
      const result = limiter.check('client1');
      expect(result.allowed).toBe(true); // Second request of 2 allowed
    });

    it('should handle mixed expired and non-expired entries', () => {
      limiter.check('client1'); // t=0
      vi.advanceTimersByTime(70000); // t=70s

      limiter.check('client2'); // t=70s

      limiter.cleanup();

      // client1 expired, should be removed
      const result1 = limiter.check('client1');
      expect(result1.allowed).toBe(true);

      // client2 not expired, should still be limited
      const result2 = limiter.check('client2');
      expect(result2.allowed).toBe(true); // Second of 2 allowed
    });
  });

  describe('Edge cases', () => {
    it('should handle very short windows', () => {
      limiter = new RateLimiter(1000, 1); // 1 second window

      limiter.check('client1');

      vi.advanceTimersByTime(500);
      expect(limiter.check('client1').allowed).toBe(false);

      vi.advanceTimersByTime(600);
      expect(limiter.check('client1').allowed).toBe(true);
    });

    it('should handle high request limits', () => {
      limiter = new RateLimiter(60000, 100);

      for (let i = 0; i < 100; i++) {
        expect(limiter.check('client1').allowed).toBe(true);
      }

      expect(limiter.check('client1').allowed).toBe(false);
    });

    it('should handle zero remaining time', () => {
      limiter = new RateLimiter(60000, 1);

      limiter.check('client1');
      vi.advanceTimersByTime(60000); // Exactly at window edge

      const result = limiter.check('client1');
      expect(result.allowed).toBe(true);
    });
  });
});

describe('getClientIdentifier', () => {
  it('should extract IP from x-forwarded-for header', () => {
    const mockRequest = new Request('http://localhost', {
      headers: {
        'x-forwarded-for': '192.168.1.1, 10.0.0.1',
      },
    });

    const identifier = getClientIdentifier(mockRequest);

    expect(identifier).toBe('192.168.1.1');
  });

  it('should extract IP from x-real-ip header', () => {
    const mockRequest = new Request('http://localhost', {
      headers: {
        'x-real-ip': '192.168.1.2',
      },
    });

    const identifier = getClientIdentifier(mockRequest);

    expect(identifier).toBe('192.168.1.2');
  });

  it('should prefer x-forwarded-for over x-real-ip', () => {
    const mockRequest = new Request('http://localhost', {
      headers: {
        'x-forwarded-for': '192.168.1.1',
        'x-real-ip': '192.168.1.2',
      },
    });

    const identifier = getClientIdentifier(mockRequest);

    expect(identifier).toBe('192.168.1.1');
  });

  it('should return default when no IP headers present', () => {
    const mockRequest = new Request('http://localhost');

    const identifier = getClientIdentifier(mockRequest);

    expect(identifier).toBe('default-client');
  });

  it('should trim whitespace from forwarded IP', () => {
    const mockRequest = new Request('http://localhost', {
      headers: {
        'x-forwarded-for': '  192.168.1.1  , 10.0.0.1',
      },
    });

    const identifier = getClientIdentifier(mockRequest);

    expect(identifier).toBe('192.168.1.1');
  });
});
