import { NextRequest, NextResponse } from 'next/server';
import { currentUser } from '@clerk/nextjs/server';
import { VerifyRequest, VerifyResponse } from '@/lib/types/api';
import { runCEGISLoop } from '@/lib/core/cegis-loop';
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
    logger.info('Verification request received', {
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
    logger.info('Parsed specification', {
      userId,
      specName,
      preconditions: spec.preconditions.length,
      invariants: spec.invariants.length,
    });

    const result = await runCEGISLoop(spec, body.maxIterations ?? 8);

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

    logger.info('Verification succeeded', {
      userId,
      specName,
      iterations: result.iterations,
      invariantsVerified: result.proofReport?.invariantsVerified.length,
    });

    return NextResponse.json<VerifyResponse>({
      success: true,
      result,
    });
  } catch (error) {
    console.error('Verification error:', error);

    const errorMessage = error instanceof Error ? error.message : 'Unknown error';

    if (
      errorMessage.toLowerCase().includes('not implemented')
    ) {
      return NextResponse.json<VerifyResponse>(
        {
          success: false,
          error:
            'Verification feature is still under development. Please try again later.',
        },
        { status: 501 }
      );
    }

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

    logger.error('Verification failed', {
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
