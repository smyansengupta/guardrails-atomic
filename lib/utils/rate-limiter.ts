/**
 * Simple in-memory rate limiter for API endpoints
 *
 * Uses IP address as identifier and stores timestamps of requests
 * to enforce rate limits per time window
 */

interface RateLimitEntry {
  timestamps: number[];
  lastReset: number;
}

class RateLimiter {
  private requests: Map<string, RateLimitEntry>;
  private windowMs: number;
  private maxRequests: number;

  constructor(windowMs: number = 60000, maxRequests: number = 1) {
    this.requests = new Map();
    this.windowMs = windowMs; // Default: 1 minute
    this.maxRequests = maxRequests; // Default: 1 request
  }

  /**
   * Check if a request should be allowed
   *
   * @param identifier - Unique identifier (e.g., IP address)
   * @returns Object with allowed status and remaining time if blocked
   */
  check(identifier: string): {
    allowed: boolean;
    remainingMs?: number;
    resetAt?: Date;
  } {
    const now = Date.now();
    const entry = this.requests.get(identifier);

    // First request from this identifier
    if (!entry) {
      this.requests.set(identifier, {
        timestamps: [now],
        lastReset: now,
      });
      return { allowed: true };
    }

    // Filter out timestamps outside the current window
    entry.timestamps = entry.timestamps.filter(
      (timestamp) => now - timestamp < this.windowMs
    );

    // Check if limit is exceeded
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

    // Allow the request and record timestamp
    entry.timestamps.push(now);
    this.requests.set(identifier, entry);

    return { allowed: true };
  }

  /**
   * Clear rate limit for a specific identifier
   */
  clear(identifier: string): void {
    this.requests.delete(identifier);
  }

  /**
   * Clear all rate limits
   */
  clearAll(): void {
    this.requests.clear();
  }

  /**
   * Cleanup old entries (run periodically)
   */
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

// Export singleton instance for generate-spec endpoint
// 1 request per minute (60000ms)
export const generateSpecLimiter = new RateLimiter(60000, 1);

// Cleanup old entries every 5 minutes
if (typeof setInterval !== 'undefined') {
  setInterval(() => {
    generateSpecLimiter.cleanup();
  }, 5 * 60 * 1000);
}

/**
 * Get client identifier from request (IP address)
 */
export function getClientIdentifier(request: Request): string {
  // Try to get real IP from headers (for proxies/load balancers)
  const forwarded = request.headers.get('x-forwarded-for');
  if (forwarded) {
    return forwarded.split(',')[0].trim();
  }

  const realIp = request.headers.get('x-real-ip');
  if (realIp) {
    return realIp;
  }

  // Fallback to a default identifier
  // Note: In serverless environments, this might not be perfect
  return 'default-client';
}
