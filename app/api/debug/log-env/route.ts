import { NextResponse } from 'next/server';

export async function GET() {
  return NextResponse.json({
    nodeEnv: process.env.NODE_ENV,
    mongoUri: process.env.MONGODB_URI ?? null,
    dbName: process.env.MONGODB_DB_NAME ?? null,
    hasUri: Boolean(process.env.MONGODB_URI),
  });
}
