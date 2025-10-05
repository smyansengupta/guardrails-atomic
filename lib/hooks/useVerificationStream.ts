'use client';

import { useState, useCallback, useRef, useEffect } from 'react';
import type { VerificationEvent, VerifyStreamRequest } from '@/lib/types/api';
import type { VerificationResult } from '@/lib/types/verification';

export interface StreamState {
  isStreaming: boolean;
  currentPhase: string;
  currentIteration: number;
  maxIterations: number;
  events: VerificationEvent[];
  result: VerificationResult | null;
  error: string | null;
}

/**
 * Custom hook for consuming Server-Sent Events from /api/verify-stream
 *
 * Usage:
 * ```typescript
 * const { streamState, startVerification, stopVerification } = useVerificationStream();
 *
 * // Start verification
 * await startVerification({ spec: yamlString });
 *
 * // Access real-time state
 * console.log(streamState.currentPhase); // "generating_code"
 * console.log(streamState.currentIteration); // 2
 * ```
 */
export function useVerificationStream() {
  const [streamState, setStreamState] = useState<StreamState>({
    isStreaming: false,
    currentPhase: '',
    currentIteration: 0,
    maxIterations: 8,
    events: [],
    result: null,
    error: null,
  });

  const eventSourceRef = useRef<EventSource | null>(null);

  // Stop streaming (cleanup)
  const stopVerification = useCallback(() => {
    if (eventSourceRef.current) {
      eventSourceRef.current.close();
      eventSourceRef.current = null;
    }
    setStreamState(prev => ({ ...prev, isStreaming: false }));
  }, []);

  // Start verification with SSE
  const startVerification = useCallback(async (request: VerifyStreamRequest) => {
    // Clean up any existing connection
    stopVerification();

    // Reset state
    setStreamState({
      isStreaming: true,
      currentPhase: 'initializing',
      currentIteration: 0,
      maxIterations: request.maxIterations ?? 8,
      events: [],
      result: null,
      error: null,
    });

    try {
      // Send POST request to initialize the stream
      const response = await fetch('/api/verify-stream', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(request),
      });

      if (!response.ok) {
        throw new Error(`HTTP ${response.status}: ${response.statusText}`);
      }

      // Check if response is SSE
      const contentType = response.headers.get('Content-Type');
      if (!contentType?.includes('text/event-stream')) {
        throw new Error('Expected SSE stream but got different content type');
      }

      // Parse SSE stream manually using Response body
      const reader = response.body?.getReader();
      const decoder = new TextDecoder();

      if (!reader) {
        throw new Error('No response body');
      }

      // Read stream
      let buffer = '';
      while (true) {
        const { done, value } = await reader.read();
        if (done) break;

        buffer += decoder.decode(value, { stream: true });

        // Process complete messages (separated by \n\n)
        const messages = buffer.split('\n\n');
        buffer = messages.pop() || ''; // Keep incomplete message in buffer

        for (const message of messages) {
          if (message.startsWith('data: ')) {
            const eventData = message.slice(6); // Remove "data: " prefix
            try {
              const event: VerificationEvent = JSON.parse(eventData);
              handleEvent(event);
            } catch (e) {
              console.error('Failed to parse event:', e);
            }
          }
        }
      }
    } catch (error) {
      setStreamState(prev => ({
        ...prev,
        isStreaming: false,
        error: error instanceof Error ? error.message : 'Unknown error',
      }));
    }
  }, [stopVerification]);

  // Handle incoming events
  const handleEvent = (event: VerificationEvent) => {
    setStreamState(prev => {
      const newState = { ...prev, events: [...prev.events, event] };

      switch (event.type) {
        case 'progress':
          newState.currentPhase = event.message;
          break;

        case 'iteration_start':
          newState.currentIteration = event.iteration;
          newState.maxIterations = event.maxIterations;
          newState.currentPhase = `Iteration ${event.iteration}/${event.maxIterations}`;
          break;

        case 'code_generated':
          newState.currentPhase = `Code generated (${event.codeLength} chars)`;
          break;

        case 'tla_generated':
          newState.currentPhase = `TLA+ generated (${event.tlaLength} chars)`;
          break;

        case 'tlc_start':
          newState.currentPhase = 'Running TLC model checker...';
          break;

        case 'tlc_complete':
          newState.currentPhase = `TLC complete - ${event.statesExplored.toLocaleString()} states`;
          break;

        case 'iteration_complete':
          newState.currentPhase = event.success
            ? `Iteration ${event.iteration} succeeded ✓`
            : `Iteration ${event.iteration} failed - repairing...`;
          break;

        case 'verification_complete':
          newState.isStreaming = false;
          newState.result = event.result || null;
          newState.currentPhase = event.success
            ? `Verification complete! ✓`
            : `Verification failed after ${event.iterations} iterations`;
          break;

        case 'error':
          newState.isStreaming = false;
          newState.error = event.message;
          newState.currentPhase = `Error: ${event.phase}`;
          break;
      }

      return newState;
    });
  };

  // Cleanup on unmount
  useEffect(() => {
    return () => {
      stopVerification();
    };
  }, [stopVerification]);

  return {
    streamState,
    startVerification,
    stopVerification,
  };
}
