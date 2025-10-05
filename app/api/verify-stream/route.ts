import { NextRequest } from 'next/server';
import { VerifyStreamRequest, VerificationEvent } from '@/lib/types/api';
import { parseSpec } from '@/lib/core/spec-parser';
import { runCEGISLoopWithEvents } from '@/lib/core/cegis-loop-stream';
import { SpecificationError } from '@/lib/utils/errors';

/**
 * SSE (Server-Sent Events) endpoint for real-time verification progress
 *
 * This endpoint streams verification events as they happen during the CEGIS loop.
 *
 * Event Flow:
 * 1. progress (parsing)
 * 2. iteration_start (iteration 1)
 * 3. progress (generating_code)
 * 4. code_generated
 * 5. progress (generating_tla)
 * 6. tla_generated
 * 7. progress (running_tlc)
 * 8. tlc_start
 * 9. tlc_complete
 * 10. iteration_complete
 * 11. [If failed] → Repeat 2-10 for iteration 2 with repair
 * 12. verification_complete
 *
 * Usage:
 * ```typescript
 * const eventSource = new EventSource('/api/verify-stream?' + params);
 * eventSource.onmessage = (event) => {
 *   const data: VerificationEvent = JSON.parse(event.data);
 *   // Handle event
 * };
 * ```
 */
export async function POST(request: NextRequest) {
  try {
    const body: VerifyStreamRequest = await request.json();

    // Validate request
    if (!body.spec) {
      return new Response(
        JSON.stringify({ type: 'error', phase: 'validation', message: 'Missing spec field', timestamp: new Date().toISOString() }),
        { status: 400, headers: { 'Content-Type': 'application/json' } }
      );
    }

    // Parse spec (validation happens inside parseSpec)
    let spec;
    try {
      spec = parseSpec(body.spec);
    } catch (error) {
      if (error instanceof SpecificationError) {
        return new Response(
          JSON.stringify({
            type: 'error',
            phase: 'parsing',
            message: `Spec validation failed: ${error.message}`,
            timestamp: new Date().toISOString()
          }),
          { status: 400, headers: { 'Content-Type': 'application/json' } }
        );
      }
      throw error;
    }

    // Create SSE stream
    const encoder = new TextEncoder();
    const stream = new ReadableStream({
      async start(controller) {
        // Helper function to send SSE event
        const sendEvent = (event: VerificationEvent) => {
          const data = `data: ${JSON.stringify(event)}\n\n`;
          controller.enqueue(encoder.encode(data));
        };

        try {
          // Run CEGIS loop with event emission
          const result = await runCEGISLoopWithEvents(
            spec,
            body.maxIterations ?? 8,
            sendEvent
          );

          // If runCEGISLoopWithEvents didn't send verification_complete, send it now
          // (This is a safety fallback - the function should handle this)
          if (!result) {
            sendEvent({
              type: 'verification_complete',
              success: false,
              iterations: 0,
              timestamp: new Date().toISOString(),
            });
          }

          controller.close();
        } catch (error) {
          // Send error event
          sendEvent({
            type: 'error',
            phase: 'unknown',
            message: error instanceof Error ? error.message : 'Unknown error',
            timestamp: new Date().toISOString(),
          });
          controller.close();
        }
      },
    });

    // Return SSE response with proper headers
    return new Response(stream, {
      headers: {
        'Content-Type': 'text/event-stream',
        'Cache-Control': 'no-cache',
        'Connection': 'keep-alive',
      },
    });
  } catch (error) {
    return new Response(
      JSON.stringify({
        type: 'error',
        phase: 'initialization',
        message: error instanceof Error ? error.message : 'Unknown error',
        timestamp: new Date().toISOString()
      }),
      { status: 500, headers: { 'Content-Type': 'application/json' } }
    );
  }
}
