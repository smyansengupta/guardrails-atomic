import { NextRequest, NextResponse } from 'next/server';
import { generateYAMLFromNL } from '@/lib/core/nl-to-yaml-generator';
import { logger } from '@/lib/utils/logger';
import { generateSpecLimiter, getClientIdentifier } from '@/lib/utils/rate-limiter';

/**
 * POST /api/generate-spec
 *
 * Converts natural language description to YAML specification
 * Rate limited to 1 request per minute per client
 *
 * @param request - Contains naturalLanguage and optional context
 * @returns Generated YAML spec with optional warnings
 */
export async function POST(req: NextRequest) {
  try {
    // Check rate limit (1 request per minute)
    const clientId = getClientIdentifier(req);
    const rateLimitResult = generateSpecLimiter.check(clientId);

    if (!rateLimitResult.allowed) {
      const remainingSeconds = Math.ceil((rateLimitResult.remainingMs || 0) / 1000);

      logger.warn('Rate limit exceeded', {
        clientId,
        remainingSeconds,
        resetAt: rateLimitResult.resetAt,
      });

      return NextResponse.json(
        {
          error: 'Rate limit exceeded. Please wait before generating another spec.',
          remainingSeconds,
          resetAt: rateLimitResult.resetAt?.toISOString(),
        },
        {
          status: 429,
          headers: {
            'Retry-After': String(remainingSeconds),
            'X-RateLimit-Limit': '1',
            'X-RateLimit-Remaining': '0',
            'X-RateLimit-Reset': rateLimitResult.resetAt?.toISOString() || '',
          },
        }
      );
    }

    const { naturalLanguage, context } = await req.json();

    // Validate input
    if (!naturalLanguage || naturalLanguage.trim().length < 10) {
      return NextResponse.json(
        { error: 'naturalLanguage is required and must be at least 10 characters' },
        { status: 400 }
      );
    }

    logger.info('Generating YAML specification', {
      clientId,
      descriptionLength: naturalLanguage.length,
      hasContext: !!context,
    });

    // Generate YAML from natural language
    const result = await generateYAMLFromNL(naturalLanguage, context);

    logger.info('Successfully generated YAML', {
      hasWarnings: !!result.warnings,
      warningCount: result.warnings?.length || 0,
    });

    return NextResponse.json(
      {
        yaml: result.yaml,
        warnings: result.warnings,
      },
      {
        headers: {
          'X-RateLimit-Limit': '1',
          'X-RateLimit-Remaining': '0', // Just used the one allowed request
        },
      }
    );
  } catch (error) {
    logger.error('Error generating YAML:', error);
    return NextResponse.json(
      { error: error instanceof Error ? error.message : 'Internal Server Error' },
      { status: 500 }
    );
  }
}
