import { describe, it, expect, vi, beforeEach } from 'vitest';
import { generateTLAModule, tlaModuleToString, generateTLCConfig } from '@/lib/verification/tla-generator';
import { generateWithOpenRouter } from '@/lib/services/openrouter.service';
import { Specification } from '@/lib/types/specification';

const sampleResponse = JSON.stringify({
  module: {
    name: 'transfer_atomic',
    extends: ['Integers', 'Sequences'],
    constants: [
      { name: 'Accts', type: 'SUBSET STRING' },
      { name: 'MaxRetries', type: 'Nat' }
    ],
    variables: [
      { name: 'balances', type: '[Accts -> Int]' },
      { name: 'processed', type: 'SUBSET STRING' }
    ],
    init: '/\\ balances = [a \\in Accts |-> 100]\n/\\ processed = {}',
    actions: [
      {
        name: 'Transfer',
        parameters: ['from', 'to', 'amt', 'req_id'],
        guards: ['req_id \\notin processed', 'amt >= 0'],
        updates: ["balances' = [balances EXCEPT ![from] = @ - amt, ![to] = @ + amt]", "processed' = processed \\union {req_id}"],
        unchanged: []
      },
      {
        name: 'DuplicateTransfer',
        parameters: ['from', 'to', 'amt', 'req_id'],
        guards: ['req_id \\in processed'],
        updates: [],
        unchanged: ['balances', 'processed']
      }
    ],
    invariants: [
      {
        name: 'TypeOK',
        predicate: '/\\ balances \\in [Accts -> Int]\n/\\ processed \\subseteq STRING',
        description: 'Type safety'
      },
      {
        name: 'Idempotent',
        predicate: '\\A req \\in processed : processed = processed',
        description: 'Duplicate requests have no effect'
      }
    ],
    next: '\\/ Transfer(from, to, amt, req_id)\\n\\/ DuplicateTransfer(from, to, amt, req_id)',
    spec: 'Init /\\ [][Next]_<<balances, processed>>',
    source: '---- MODULE transfer_atomic ----\nEXTENDS Integers, Sequences\nVARIABLES balances, processed\n====='
  },
  config: 'CONSTANTS\n  Accts = {"a1", "a2", "a3"}\n  MaxRetries = 2\n\nINIT Init\nNEXT Next\nINVARIANTS\n  Idempotent'
});

vi.mock('@/lib/services/openrouter.service', () => ({
  generateWithOpenRouter: vi.fn(),
}));

describe('tla-generator', () => {
  const mockSpec: Specification = {
    name: 'transfer_atomic',
    signature: {
      params: [
        { name: 'state', type: 'Map<Acct,int>' },
        { name: 'from', type: 'Acct' },
        { name: 'to', type: 'Acct' },
        { name: 'amt', type: 'int' },
        { name: 'req_id', type: 'UUID' },
      ],
      returnType: 'Map<Acct,int>',
    },
    preconditions: ['amt >= 0'],
    postconditions: ['sum(result.values()) == sum(state.values())'],
    invariants: [{ type: 'idempotent' }],
    faultModel: {
      delivery: 'at_least_once',
      reorder: true,
      crash_restart: true,
    },
    bounds: {
      accts: 3,
      retries: 2,
    },
  };

beforeEach(() => {
  vi.clearAllMocks();
  vi.mocked(generateWithOpenRouter).mockResolvedValue(sampleResponse);
});

  it('generates a TLA+ module via OpenRouter', async () => {
    const module = await generateTLAModule(mockSpec);
    expect(module.name).toBe('transfer_atomic');
    expect(module.extends).toContain('Integers');
    expect(module.variables).toHaveLength(2);
    expect(module.actions[0].parameters).toContain('req_id');
    expect(module.invariants.find(inv => inv.name === 'TypeOK')).toBeDefined();
    expect(module.source).toContain('---- MODULE transfer_atomic ----');
  });

  it('serialises module source transparently', async () => {
    const module = await generateTLAModule(mockSpec);
    const tlaString = tlaModuleToString(module);
    expect(tlaString.startsWith('---- MODULE transfer_atomic ----')).toBe(true);
    expect(tlaString.trim().endsWith('=====')).toBe(true);
  });

  it('provides TLC configuration from cached response', async () => {
    await generateTLAModule(mockSpec);
    const config = await generateTLCConfig(mockSpec);
    expect(config).toContain('CONSTANTS');
    expect(config).toContain('INIT Init');
    expect(config).toContain('INVARIANTS');
  });
});
