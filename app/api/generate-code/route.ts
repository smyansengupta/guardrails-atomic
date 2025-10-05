import { NextRequest, NextResponse } from 'next/server';
import { currentUser } from '@clerk/nextjs/server';
import { parseSpec } from '@/lib/core/spec-parser';
import { generateCode } from '@/lib/core/code-generator';
import { saveVerificationLog } from '@/lib/history/persistence';

export interface GenerateCodeRequest {
  spec: string; // YAML string
}

export interface GenerateCodeResponse {
  success: boolean;
  code?: string;
  error?: string;
}

export async function POST(request: NextRequest) {
  const user = await currentUser();
  const userId = user?.id;
  let startedAt: number | undefined;
  let specName: string | undefined;
  let specYaml: string | undefined;

  try {
    const body: GenerateCodeRequest = await request.json();
    specYaml = body.spec;

    // Validate request
    if (!body.spec) {
      return NextResponse.json<GenerateCodeResponse>(
        { success: false, error: 'Missing spec field' },
        { status: 400 }
      );
    }

    // Parse spec
    const spec = parseSpec(body.spec);
    specName = spec.name;
    startedAt = Date.now();

    // Generate code only (no verification)
    const code = await generateCode(spec);

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
            finalCode: code,
          },
        });
      } catch (historyError) {
        console.warn('Failed to persist code-only history:', historyError);
      }
    }

    return NextResponse.json<GenerateCodeResponse>({
      success: true,
      code,
    });
  } catch (error) {
    console.error('Code generation error:', error);

    const errorMessage = error instanceof Error ? error.message : 'Unknown error';

    if (userId && specYaml) {
      try {
        await saveVerificationLog({
          userId,
          spec: specYaml,
          specName,
          success: false,
          iterations: 0,
          durationMs: undefined,
          result: {
            success: false,
            iterations: 0,
            error: errorMessage,
          },
        });
      } catch (historyError) {
        console.warn('Failed to persist code-only failure:', historyError);
      }
    }

    return NextResponse.json<GenerateCodeResponse>(
      {
        success: false,
        error: errorMessage
      },
      { status: 500 }
    );
  }
}
