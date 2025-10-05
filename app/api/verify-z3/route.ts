/**
 * Z3-based verification endpoint
 * 
 * This endpoint uses Z3 SMT solver instead of TLA+/TLC for formal verification.
 */

import { NextRequest, NextResponse } from 'next/server';
import { currentUser } from '@clerk/nextjs/server';
import { VerifyRequest, VerifyResponse } from '@/lib/types/api';
import { runCEGISLoopZ3 } from '@/lib/core/cegis-loop-z3';
import { parseSpec } from '@/lib/core/spec-parser';
import { saveVerificationLog } from '@/lib/history/persistence';
import { logger } from '@/lib/utils/logger';

export async function POST(request: NextRequest) {
  const user = await currentUser();

  if (!user) {
    return NextResponse.json<VerifyResponse>(
      { success: false, error: 'Authentication required' },
      { status: 401 }
    );
  }

  const userId = user.id;

  let specName: string | undefined;
  let specYaml: string | undefined;
  const startedAt = Date.now();

  try {
    const body: VerifyRequest = await request.json();
    specYaml = body.spec;
    logger.info('Z3 verification request received', {
      userId,
      hasSpec: Boolean(body?.spec),
      maxIterations: body?.maxIterations,
    });

    if (!body.spec) {
      return NextResponse.json<VerifyResponse>(
        { success: false, error: 'Missing spec field' },
        { status: 400 }
      );
    }

    const spec = parseSpec(body.spec);
    specName = spec.name;
    logger.info('Parsed specification for Z3 verification', {
      userId,
      specName,
      preconditions: spec.preconditions.length,
      invariants: spec.invariants.length,
    });

    // Run CEGIS loop with Z3
    const result = await runCEGISLoopZ3(spec, body.maxIterations ?? 8);

    // Save to history
    try {
      await saveVerificationLog({
        userId,
        spec: body.spec,
        specName,
        success: result.success,
        iterations: result.iterations,
        durationMs: Date.now() - startedAt,
        result,
      });
    } catch (historyError) {
      console.warn('Failed to persist verification history:', historyError);
    }

    logger.info('Z3 verification completed', {
      userId,
      specName,
      success: result.success,
      iterations: result.iterations,
      invariantsVerified: result.proofReport?.invariantsVerified.length,
    });

    return NextResponse.json<VerifyResponse>({
      success: true,
      result,
    });
  } catch (error) {
    console.error('Z3 verification error:', error);

    const errorMessage = error instanceof Error ? error.message : 'Unknown error';

    // Save failed attempt
    if (specYaml) {
      try {
        await saveVerificationLog({
          userId,
          spec: specYaml,
          specName,
          success: false,
          iterations: 0,
          durationMs: Date.now() - startedAt,
          result: {
            success: false,
            iterations: 0,
            error: errorMessage,
          },
        });
      } catch (historyError) {
        console.warn('Failed to persist failed verification history:', historyError);
      }
    }

    logger.error('Z3 verification failed', {
      userId,
      specName,
      error: errorMessage,
    });

    return NextResponse.json<VerifyResponse>(
      {
        success: false,
        error: errorMessage,
      },
      { status: 500 }
    );
  }
}

