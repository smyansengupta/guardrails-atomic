import { NextRequest, NextResponse } from 'next/server';
import { currentUser } from '@clerk/nextjs/server';
import { parseSpec } from '@/lib/core/spec-parser';
import { generateZ3Module, z3ModuleToString, generateZ3Config } from '@/lib/verification/z3-generator';
import { saveVerificationLog } from '@/lib/history/persistence';
import { logger } from '@/lib/utils/logger';

export interface GenerateTLARequest {
  spec: string; // YAML string
}

export interface GenerateTLAResponse {
  success: boolean;
  tlaSpec?: string; // Actually Z3 constraints (kept for backward compatibility with frontend)
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

    logger.info('Generating Z3 SMT specification', {
      userId,
      specName,
    });

    // Generate Z3 constraints and config
    const z3Module = generateZ3Module(spec);
    const z3Constraints = z3ModuleToString(z3Module);
    const z3Config = generateZ3Config(spec);

    logger.info('Z3 constraint generation successful', {
      userId,
      specName,
      constraintsLength: z3Constraints.length,
      configLength: z3Config.length,
    });

    // Log the generated Z3 constraints for debugging
    logger.debug('Generated Z3 constraints:\n' + '='.repeat(80) + '\n' + z3Constraints + '\n' + '='.repeat(80));
    logger.debug('Generated Z3 config:\n' + '='.repeat(80) + '\n' + z3Config + '\n' + '='.repeat(80));

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
            z3Constraints,
          },
        });
      } catch (historyError) {
        console.warn('Failed to persist Z3 generation history:', historyError);
      }
    }

    return NextResponse.json<GenerateTLAResponse>({
      success: true,
      tlaSpec: z3Constraints, // Use field name for backward compatibility
      tlaConfig: z3Config,
    });
  } catch (error) {
    console.error('Z3 constraint generation error:', error);

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
        console.warn('Failed to persist Z3 generation failure:', historyError);
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
