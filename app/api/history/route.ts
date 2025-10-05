import { NextRequest, NextResponse } from 'next/server';
import { currentUser } from '@clerk/nextjs/server';
import { listVerificationLogs, saveVerificationLog } from '@/lib/history/persistence';

export async function GET(request: NextRequest) {
  const user = await currentUser();

  if (!user) {
    return NextResponse.json({ error: 'Authentication required' }, { status: 401 });
  }

  const userId = user.id;

  const searchParams = request.nextUrl.searchParams;
  const cursor = searchParams.get('cursor') ?? undefined;
  const limitParam = searchParams.get('limit');
  const limit = limitParam ? Math.min(Math.max(parseInt(limitParam, 10) || 20, 1), 100) : 20;

  try {
    const history = await listVerificationLogs(userId, limit, cursor);
    return NextResponse.json(history, { status: 200 });
  } catch (error) {
    console.error('Failed to fetch verification history:', error);
    return NextResponse.json({ error: 'Failed to fetch verification history' }, { status: 500 });
  }
}

export async function POST(request: NextRequest) {
  const user = await currentUser();

  if (!user) {
    return NextResponse.json({ error: 'Authentication required' }, { status: 401 });
  }

  const userId = user.id;

  try {
    const payload = await request.json();

    if (!payload?.spec || typeof payload.spec !== 'string' || !payload?.result) {
      return NextResponse.json({ error: 'Invalid payload' }, { status: 400 });
    }

    const record = await saveVerificationLog({
      userId,
      spec: payload.spec,
      specName: payload.specName,
      success: !!payload.success,
      iterations: Number(payload.iterations) || 0,
      durationMs: payload.durationMs ? Number(payload.durationMs) : undefined,
      result: payload.result,
    });

    return NextResponse.json(record, { status: 201 });
  } catch (error) {
    console.error('Failed to persist verification history:', error);
    return NextResponse.json({ error: 'Failed to persist verification history' }, { status: 500 });
  }
}
