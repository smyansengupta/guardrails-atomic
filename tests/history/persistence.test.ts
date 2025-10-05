import { describe, expect, it, vi, beforeEach } from 'vitest';
import { saveVerificationLog, listVerificationLogs } from '@/lib/history/persistence';
import type { VerificationResult } from '@/lib/types/verification';

const insertOne = vi.fn();
const find = vi.fn();
const sort = vi.fn();
const limit = vi.fn();
const toArray = vi.fn();

vi.mock('@/lib/db/mongodb', () => ({
  getMongoDb: async () => ({
    collection: () => ({
      insertOne,
      find,
      sort,
      limit,
      toArray,
    }),
  }),
}));

const baseResult: VerificationResult = {
  success: true,
  iterations: 1,
  finalCode: 'console.log(1);',
};

beforeEach(() => {
  insertOne.mockReset();
  find.mockReset();
  sort.mockReset();
  limit.mockReset();
  toArray.mockReset();

  find.mockReturnValue({ sort });
  sort.mockReturnValue({ limit });
  limit.mockReturnValue({ toArray });
});

describe('saveVerificationLog', () => {
  it('persists verification data and returns mapped record', async () => {
    const fakeId = { toHexString: () => 'abc123' } as any;

    insertOne.mockResolvedValue({ insertedId: fakeId });

    const record = await saveVerificationLog({
      userId: 'user_1',
      spec: 'name: TestSpec',
      specName: 'TestSpec',
      success: true,
      iterations: 2,
      durationMs: 42,
      result: baseResult,
    });

    expect(insertOne).toHaveBeenCalledTimes(1);
    expect(record).toMatchObject({
      id: 'abc123',
      userId: 'user_1',
      success: true,
      iterations: 2,
      result: baseResult,
    });
    expect(new Date(record.createdAt).toString()).not.toBe('Invalid Date');
  });
});

describe('listVerificationLogs', () => {
  it('returns mapped history items and next cursor', async () => {
    const docs = [
      {
        _id: { toHexString: () => 'id1' },
        createdAt: new Date('2024-01-01T00:00:00Z'),
        userId: 'user_1',
        spec: 'spec',
        specName: 'Spec',
        success: true,
        iterations: 1,
        durationMs: 10,
        result: baseResult,
      },
      {
        _id: { toHexString: () => 'id0' },
        createdAt: new Date('2023-12-31T00:00:00Z'),
        userId: 'user_1',
        spec: 'spec2',
        specName: 'Spec2',
        success: false,
        iterations: 0,
        durationMs: 5,
        result: { ...baseResult, success: false },
      },
    ];

    toArray.mockResolvedValue(docs);

    const result = await listVerificationLogs('user_1', 1);

    expect(find).toHaveBeenCalledWith({ userId: 'user_1' });
    expect(result.items).toHaveLength(1);
    expect(result.items[0]).toMatchObject({ id: 'id1', specName: 'Spec' });
    expect(result.nextCursor).toBe('id1');
  });
});
