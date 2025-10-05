'use client';

import { useState, useCallback, useEffect, useRef } from 'react';
import { GenerateSpecResponse } from '@/lib/types/api';

interface UseGenerateSpecOptions {
  onSuccess?: (yaml: string, warnings?: string[]) => void;
  onError?: (error: string) => void;
}

interface UseGenerateSpecReturn {
  generateSpec: (naturalLanguage: string, context?: string) => Promise<void>;
  isLoading: boolean;
  error: string | null;
  yaml: string | null;
  warnings: string[] | null;
  remainingSeconds: number;
  canGenerate: boolean;
  resetTimer: () => void;
}

/**
 * Custom hook for generating YAML specs from natural language
 *
 * Features:
 * - Automatic rate limiting (1 request per minute)
 * - Countdown timer showing remaining time
 * - Loading and error states
 * - Success/error callbacks
 *
 * @example
 * const { generateSpec, isLoading, canGenerate, remainingSeconds } = useGenerateSpec({
 *   onSuccess: (yaml) => console.log('Generated:', yaml),
 *   onError: (error) => console.error('Error:', error),
 * });
 */
export function useGenerateSpec(options?: UseGenerateSpecOptions): UseGenerateSpecReturn {
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [yaml, setYaml] = useState<string | null>(null);
  const [warnings, setWarnings] = useState<string[] | null>(null);
  const [remainingSeconds, setRemainingSeconds] = useState(0);
  const [canGenerate, setCanGenerate] = useState(true);
  const timerRef = useRef<NodeJS.Timeout | null>(null);

  // Cleanup timer on unmount
  useEffect(() => {
    return () => {
      if (timerRef.current) {
        clearInterval(timerRef.current);
      }
    };
  }, []);

  // Start countdown timer
  const startTimer = useCallback((seconds: number) => {
    setRemainingSeconds(seconds);
    setCanGenerate(false);

    // Clear existing timer if any
    if (timerRef.current) {
      clearInterval(timerRef.current);
    }

    // Update every second
    timerRef.current = setInterval(() => {
      setRemainingSeconds((prev) => {
        if (prev <= 1) {
          if (timerRef.current) {
            clearInterval(timerRef.current);
            timerRef.current = null;
          }
          setCanGenerate(true);
          return 0;
        }
        return prev - 1;
      });
    }, 1000);
  }, []);

  const resetTimer = useCallback(() => {
    if (timerRef.current) {
      clearInterval(timerRef.current);
      timerRef.current = null;
    }
    setRemainingSeconds(0);
    setCanGenerate(true);
  }, []);

  const generateSpec = useCallback(
    async (naturalLanguage: string, context?: string) => {
      if (!canGenerate) {
        setError(`Please wait ${remainingSeconds} seconds before generating again`);
        return;
      }

      setIsLoading(true);
      setError(null);
      setYaml(null);
      setWarnings(null);

      try {
        const response = await fetch('/api/generate-spec', {
          method: 'POST',
          headers: {
            'Content-Type': 'application/json',
          },
          body: JSON.stringify({
            naturalLanguage,
            context,
          }),
        });

        const data: GenerateSpecResponse & {
          remainingSeconds?: number;
          resetAt?: string;
        } = await response.json();

        // Handle rate limiting
        if (response.status === 429) {
          const seconds = data.remainingSeconds || 60;
          startTimer(seconds);
          const errorMsg = data.error || 'Rate limit exceeded. Please wait before trying again.';
          setError(errorMsg);
          options?.onError?.(errorMsg);
          return;
        }

        // Handle other errors
        if (!response.ok || data.error) {
          const errorMsg = data.error || 'Failed to generate specification';
          setError(errorMsg);
          options?.onError?.(errorMsg);
          return;
        }

        // Success
        if (data.yaml) {
          setYaml(data.yaml);
          setWarnings(data.warnings || null);
          options?.onSuccess?.(data.yaml, data.warnings);

          // Start 60 second cooldown after successful generation
          startTimer(60);
        }
      } catch (err) {
        const errorMsg = err instanceof Error ? err.message : 'An unexpected error occurred';
        setError(errorMsg);
        options?.onError?.(errorMsg);
      } finally {
        setIsLoading(false);
      }
    },
    [canGenerate, remainingSeconds, startTimer, options]
  );

  return {
    generateSpec,
    isLoading,
    error,
    yaml,
    warnings,
    remainingSeconds,
    canGenerate,
    resetTimer,
  };
}
