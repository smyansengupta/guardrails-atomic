import { NextRequest, NextResponse } from 'next/server';
import { currentUser } from '@clerk/nextjs/server';
import { parseSpec } from '@/lib/core/spec-parser';
import { generateTLAModule, tlaModuleToString, generateTLCConfig } from '@/lib/verification/tla-generator';
import { saveVerificationLog } from '@/lib/history/persistence';
import { logger } from '@/lib/utils/logger';

export interface GenerateTLARequest {
  spec: string; // YAML string
}

export interface GenerateTLAResponse {
  success: boolean;
  tlaSpec?: string;
  tlaConfig?: string;
  error?: string;
}

export async function POST(request: NextRequest) {
  const user = await currentUser();
  const userId = user?.id;
  let startedAt: number | undefined;
  let specName: string | undefined;
  let specYaml: string | undefined;

  try {
    const body: GenerateTLARequest = await request.json();
    specYaml = body.spec;

    // Validate request
    if (!body.spec) {
      return NextResponse.json<GenerateTLAResponse>(
        { success: false, error: 'Missing spec field' },
        { status: 400 }
      );
    }

    // Parse spec
    const spec = parseSpec(body.spec);
    specName = spec.name;
    startedAt = Date.now();

    logger.info('Generating TLA+ specification', {
      userId,
      specName,
    });

    // Generate TLA+ spec and config
    const tlaModule = await generateTLAModule(spec);
    const tlaSpec = tlaModuleToString(tlaModule);
    const tlaConfig = await generateTLCConfig(spec);

    logger.info('TLA+ generation successful', {
      userId,
      specName,
      tlaLength: tlaSpec.length,
      configLength: tlaConfig.length,
    });

    // Log the generated TLA+ for debugging
    logger.debug('Generated TLA+ specification:\n' + '='.repeat(80) + '\n' + tlaSpec + '\n' + '='.repeat(80));
    logger.debug('Generated TLC config:\n' + '='.repeat(80) + '\n' + tlaConfig + '\n' + '='.repeat(80));

    if (userId) {
      try {
        await saveVerificationLog({
          userId,
          spec: body.spec,
          specName,
          success: true,
          iterations: 0,
          durationMs: Date.now() - startedAt,
          result: {
            success: true,
            iterations: 0,
            tlaSpec,
          },
        });
      } catch (historyError) {
        console.warn('Failed to persist TLA+ generation history:', historyError);
      }
    }

    return NextResponse.json<GenerateTLAResponse>({
      success: true,
      tlaSpec,
      tlaConfig,
    });
  } catch (error) {
    console.error('TLA+ generation error:', error);

    const errorMessage = error instanceof Error ? error.message : 'Unknown error';

    if (userId && specYaml) {
      try {
        await saveVerificationLog({
          userId,
          spec: specYaml,
          specName,
          success: false,
          iterations: 0,
          durationMs: startedAt ? Date.now() - startedAt : undefined,
          result: {
            success: false,
            iterations: 0,
            error: errorMessage,
          },
        });
      } catch (historyError) {
        console.warn('Failed to persist TLA+ generation failure:', historyError);
      }
    }

    return NextResponse.json<GenerateTLAResponse>(
      {
        success: false,
        error: errorMessage
      },
      { status: 500 }
    );
  }
}
