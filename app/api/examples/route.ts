import { NextResponse } from 'next/server';
import { ExamplesResponse } from '@/lib/types/api';
import { readFile } from 'fs/promises';
import path from 'path';

export async function GET() {
  try {
    const templatesDir = path.join(process.cwd(), 'templates', 'specs');

    const transfer = await readFile(
      path.join(templatesDir, 'transfer.yaml'),
      'utf-8'
    );
    const idempotentWrite = await readFile(
      path.join(templatesDir, 'idempotent-write.yaml'),
      'utf-8'
    );

    return NextResponse.json<ExamplesResponse>({
      examples: [
        {
          name: 'Atomic Transfer',
          description: 'Money transfer with conservation and idempotency',
          yaml: transfer,
          category: 'transfer',
        },
        {
          name: 'Idempotent Write',
          description: 'Write operation safe under duplicate delivery',
          yaml: idempotentWrite,
          category: 'write',
        },
      ],
    });
  } catch (error) {
    return NextResponse.json(
      { error: 'Failed to load examples' },
      { status: 500 }
    );
  }
}
