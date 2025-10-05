import { NextRequest, NextResponse } from 'next/server';
import { ValidateRequest, ValidateResponse } from '@/lib/types/api';
import { parseSpec } from '@/lib/core/spec-parser';

export async function POST(request: NextRequest) {
  try {
    const body: ValidateRequest = await request.json();

    if (!body.spec) {
      return NextResponse.json<ValidateResponse>(
        { valid: false, errors: ['Missing spec field'] },
        { status: 400 }
      );
    }

    const parsed = parseSpec(body.spec);

    return NextResponse.json<ValidateResponse>({
      valid: true,
      parsed,
    });
  } catch (error) {
    return NextResponse.json<ValidateResponse>({
      valid: false,
      errors: [error instanceof Error ? error.message : 'Invalid spec'],
    });
  }
}
