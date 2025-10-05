import { ObjectId, WithId } from 'mongodb';
import { getMongoDb } from '@/lib/db/mongodb';
import { VerificationResult } from '@/lib/types/verification';
import { logger } from '@/lib/utils/logger';

const COLLECTION = 'verification_logs';

export interface VerificationLogInput {
  userId: string;
  spec: string;
  specName?: string;
  success: boolean;
  iterations: number;
  durationMs?: number;
  result: VerificationResult;
}

export interface VerificationLogRecord {
  id: string;
  userId: string;
  spec: string;
  specName?: string;
  success: boolean;
  iterations: number;
  durationMs?: number;
  createdAt: string;
  result: VerificationResult;
}

type VerificationLogDocument = Omit<VerificationLogRecord, 'id' | 'createdAt'> & {
  _id: ObjectId;
  createdAt: Date;
};

function mapDocument(doc: WithId<VerificationLogDocument>): VerificationLogRecord {
  const { _id, createdAt, ...rest } = doc;
  return {
    id: _id.toHexString(),
    createdAt: createdAt.toISOString(),
    ...rest,
  };
}

export async function saveVerificationLog(input: VerificationLogInput): Promise<VerificationLogRecord> {
  const db = await getMongoDb();
  const collection = db.collection<VerificationLogDocument>(COLLECTION);

  const document: Omit<VerificationLogDocument, '_id'> = {
    userId: input.userId,
    spec: input.spec,
    specName: input.specName,
    success: input.success,
    iterations: input.iterations,
    durationMs: input.durationMs,
    createdAt: new Date(),
    result: input.result,
  };

  const { insertedId } = await collection.insertOne(document as VerificationLogDocument);

  const saved = mapDocument({ ...(document as VerificationLogDocument), _id: insertedId });
  logger.info('Persisted verification log entry', {
    userId: saved.userId,
    id: saved.id,
    success: saved.success,
    iterations: saved.iterations,
  });

  return saved;
}

export async function listVerificationLogs(
  userId: string,
  limit = 20,
  cursor?: string
): Promise<{ items: VerificationLogRecord[]; nextCursor?: string }> {
  const db = await getMongoDb();
  const collection = db.collection<VerificationLogDocument>(COLLECTION);

  const filters: Record<string, unknown> = { userId };

  if (cursor) {
    try {
      filters._id = { $lt: new ObjectId(cursor) };
    } catch (error) {
      logger.warn('Invalid history cursor supplied', { cursor, error });
    }
  }

  const docs = await collection
    .find(filters)
    .sort({ _id: -1 })
    .limit(limit + 1)
    .toArray();

  const hasMore = docs.length > limit;
  const items = docs.slice(0, limit).map(mapDocument);
  const nextCursor = hasMore ? items[items.length - 1]?.id : undefined;

  return { items, nextCursor };
}
