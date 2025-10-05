import { describe, it, expect, vi, beforeEach } from 'vitest';
import { runCEGISLoop } from '@/lib/core/cegis-loop';
import { Specification } from '@/lib/types/specification';
import { TLCResult } from '@/lib/types/verification';
import * as codeGenerator from '@/lib/core/code-generator';
import * as tlaGenerator from '@/lib/verification/tla-generator';
import * as tlcRunner from '@/lib/verification/tlc-runner';
import * as counterexampleParser from '@/lib/verification/counterexample-parser';

// Mock all dependencies
vi.mock('@/lib/core/code-generator');
vi.mock('@/lib/verification/tla-generator');
vi.mock('@/lib/verification/tlc-runner');
vi.mock('@/lib/verification/counterexample-parser');

describe('cegis-loop', () => {
  const mockSpec: Specification = {
    name: 'test_transfer',
    signature: {
      params: [
        { name: 'from', type: 'string' },
        { name: 'to', type: 'string' },
        { name: 'amount', type: 'number' },
        { name: 'requestId', type: 'string' },
      ],
      returnType: 'void',
    },
    preconditions: ['balance[from] >= amount'],
    postconditions: ['balance[to] == old(balance[to]) + amount'],
    invariants: [
      { type: 'idempotent', description: 'Duplicate requests have no effect' },
      { type: 'conservation', description: 'Total balance is conserved' },
    ],
    faultModel: {
      delivery: 'at_least_once',
      reorder: false,
      crash_restart: false,
    },
    bounds: {
      accts: 3,
      retries: 2,
      messages: 5,
      depth: 10,
    },
  };

  const mockGeneratedCode = `
    function transfer(from: string, to: string, amount: number, requestId: string) {
      if (processed.has(requestId)) return;
      balance[from] -= amount;
      balance[to] += amount;
      processed.add(requestId);
    }
  `;

  const mockTLASpec = `
    ---- MODULE Transfer ----
    EXTENDS Integers
    VARIABLES balance, processed
    ====
  `;

  const mockTLAConfig = `
    INIT Init
    NEXT Next
    INVARIANT Conservation
  `;

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('successful verification', () => {
    it('should verify on first iteration', async () => {
      // Mock successful verification
      vi.mocked(codeGenerator.generateCode).mockResolvedValue(mockGeneratedCode);
      vi.mocked(tlaGenerator.generateTLAModule).mockResolvedValue({
        name: 'Transfer',
        extends: ['Integers'],
        constants: [],
        variables: [],
        init: 'Init',
        actions: [],
        invariants: [],
        next: 'Next',
        spec: 'Spec',
        source: mockTLASpec,
      });
      vi.mocked(tlaGenerator.tlaModuleToString).mockReturnValue(mockTLASpec);
      vi.mocked(tlaGenerator.generateTLCConfig).mockResolvedValue(mockTLAConfig);

      const mockTLCResult: TLCResult = {
        success: true,
        statesExplored: 42,
        invariantsChecked: ['TypeOK', 'Conservation', 'Idempotent'],
        output: 'Model checking completed successfully',
        duration: 1500,
      };
      vi.mocked(tlcRunner.runTLC).mockResolvedValue(mockTLCResult);

      const result = await runCEGISLoop(mockSpec, 8);

      expect(result.success).toBe(true);
      expect(result.iterations).toBe(1);
      expect(result.finalCode).toBe(mockGeneratedCode);
      expect(result.proofReport).toBeDefined();
      expect(result.proofReport?.statesExplored).toBe(42);
      expect(result.proofReport?.invariantsVerified).toEqual(['TypeOK', 'Conservation', 'Idempotent']);
      expect(result.iterationHistory).toHaveLength(1);
    });

    it('should include fault scenarios in proof report', async () => {
      vi.mocked(codeGenerator.generateCode).mockResolvedValue(mockGeneratedCode);
      vi.mocked(tlaGenerator.generateTLAModule).mockResolvedValue({ source: mockTLASpec } as any);
      vi.mocked(tlaGenerator.tlaModuleToString).mockReturnValue(mockTLASpec);
      vi.mocked(tlaGenerator.generateTLCConfig).mockResolvedValue(mockTLAConfig);

      const mockTLCResult: TLCResult = {
        success: true,
        statesExplored: 100,
        invariantsChecked: ['TypeOK'],
        output: 'Success',
      };
      vi.mocked(tlcRunner.runTLC).mockResolvedValue(mockTLCResult);

      const result = await runCEGISLoop(mockSpec, 8);

      expect(result.proofReport?.faultScenariosChecked).toContain('Duplicate message delivery');
      expect(result.proofReport?.guarantees).toContain('Function is idempotent - duplicate requests have no additional effect');
      expect(result.proofReport?.guarantees).toContain('Total resources are conserved across all operations');
    });
  });

  describe('repair loop', () => {
    it('should repair code after violation and verify on second iteration', async () => {
      const brokenCode = 'function broken() {}';
      const fixedCode = 'function fixed() {}';

      // Mock generateRepairFeedback to return the expected feedback
      const mockFeedback = 'Fix: Check if requestId is in processed set';
      vi.mocked(counterexampleParser.generateRepairFeedback).mockReturnValue(mockFeedback);

      // First iteration: code generation + violation
      vi.mocked(codeGenerator.generateCode)
        .mockResolvedValueOnce(brokenCode)
        .mockResolvedValueOnce(fixedCode);

      vi.mocked(tlaGenerator.generateTLAModule).mockResolvedValue({ source: mockTLASpec } as any);
      vi.mocked(tlaGenerator.tlaModuleToString).mockReturnValue(mockTLASpec);
      vi.mocked(tlaGenerator.generateTLCConfig).mockResolvedValue(mockTLAConfig);

      // First iteration: violation
      const violationResult: TLCResult = {
        success: false,
        statesExplored: 10,
        invariantsChecked: [],
        violations: [
          {
            invariantName: 'Idempotent',
            message: 'Duplicate request changed state',
          },
        ],
        counterExample: {
          schedule: [
            { action: 'Transfer', state: { balance: { a1: 100, a2: 100 } } },
            { action: 'DuplicateTransfer', state: { balance: { a1: 50, a2: 50 } } },
          ],
          violation: {
            invariantName: 'Idempotent',
            message: 'Duplicate request changed state',
          },
          suggestedFix: 'Check if requestId is in processed set before executing',
        },
        output: 'Invariant violated',
      };

      // Second iteration: success
      const successResult: TLCResult = {
        success: true,
        statesExplored: 50,
        invariantsChecked: ['TypeOK', 'Idempotent'],
        output: 'Success',
      };

      vi.mocked(tlcRunner.runTLC)
        .mockResolvedValueOnce(violationResult)
        .mockResolvedValueOnce(successResult);

      const result = await runCEGISLoop(mockSpec, 8);

      expect(result.success).toBe(true);
      expect(result.iterations).toBe(2);
      expect(result.finalCode).toBe(fixedCode);
      expect(result.iterationHistory).toHaveLength(2);

      // Check that repair feedback was passed to second code generation
      expect(codeGenerator.generateCode).toHaveBeenNthCalledWith(1, mockSpec, undefined);
      const secondInvocation = vi.mocked(codeGenerator.generateCode).mock.calls[1][1] as string;
      expect(secondInvocation).toContain('ORIGINAL CODE');
      expect(secondInvocation).toContain(mockFeedback);
    });

    it('should handle violations without counterexample', async () => {
      vi.mocked(codeGenerator.generateCode).mockResolvedValue(mockGeneratedCode);
      vi.mocked(tlaGenerator.generateTLAModule).mockResolvedValue({ source: mockTLASpec } as any);
      vi.mocked(tlaGenerator.tlaModuleToString).mockReturnValue(mockTLASpec);
      vi.mocked(tlaGenerator.generateTLCConfig).mockResolvedValue(mockTLAConfig);

      const violationResult: TLCResult = {
        success: false,
        statesExplored: 10,
        invariantsChecked: [],
        violations: [
          {
            invariantName: 'Conservation',
            message: 'Total balance changed',
          },
        ],
        output: 'Invariant violated',
      };

      const successResult: TLCResult = {
        success: true,
        statesExplored: 50,
        invariantsChecked: ['Conservation'],
        output: 'Success',
      };

      vi.mocked(tlcRunner.runTLC)
        .mockResolvedValueOnce(violationResult)
        .mockResolvedValueOnce(successResult);

      const result = await runCEGISLoop(mockSpec, 8);

      expect(result.success).toBe(true);
      expect(result.iterations).toBe(2);

      // Should have generated feedback from violations
      const secondCallFeedback = vi.mocked(codeGenerator.generateCode).mock.calls[1][1];
      expect(secondCallFeedback).toContain('Conservation');
      expect(secondCallFeedback).toContain('Total balance changed');
    });
  });

  describe('failure cases', () => {
    it('should fail after max iterations', async () => {
      vi.mocked(codeGenerator.generateCode).mockResolvedValue(mockGeneratedCode);
      vi.mocked(tlaGenerator.generateTLAModule).mockResolvedValue({ source: mockTLASpec } as any);
      vi.mocked(tlaGenerator.tlaModuleToString).mockReturnValue(mockTLASpec);
      vi.mocked(tlaGenerator.generateTLCConfig).mockResolvedValue(mockTLAConfig);

      const violationResult: TLCResult = {
        success: false,
        statesExplored: 10,
        invariantsChecked: [],
        violations: [
          {
            invariantName: 'Idempotent',
            message: 'Failed',
          },
        ],
        output: 'Failed',
      };

      vi.mocked(tlcRunner.runTLC).mockResolvedValue(violationResult);

      const result = await runCEGISLoop(mockSpec, 3);

      expect(result.success).toBe(false);
      expect(result.iterations).toBe(3);
      expect(result.error).toContain('Max iterations (3) reached');
      expect(result.iterationHistory).toHaveLength(3);
    });

    it('should handle code generation errors', async () => {
      vi.mocked(codeGenerator.generateCode).mockRejectedValue(
        new Error('API rate limit exceeded')
      );

      const result = await runCEGISLoop(mockSpec, 8);

      expect(result.success).toBe(false);
      expect(result.error).toContain('Code generation failed');
      expect(result.error).toContain('API rate limit exceeded');
    });

    it('should handle TLA+ generation errors', async () => {
      vi.mocked(codeGenerator.generateCode).mockResolvedValue(mockGeneratedCode);
      vi.mocked(tlaGenerator.generateTLAModule).mockImplementation(async () => {
        throw new Error('Invalid TLA+ syntax');
      });

      const result = await runCEGISLoop(mockSpec, 8);

      expect(result.success).toBe(false);
      expect(result.error).toContain('TLA+ generation failed');
      expect(result.error).toContain('Invalid TLA+ syntax');
    });

    it('should handle TLC execution errors', async () => {
      vi.mocked(codeGenerator.generateCode).mockResolvedValue(mockGeneratedCode);
      vi.mocked(tlaGenerator.generateTLAModule).mockResolvedValue({ source: mockTLASpec } as any);
      vi.mocked(tlaGenerator.tlaModuleToString).mockReturnValue(mockTLASpec);
      vi.mocked(tlaGenerator.generateTLCConfig).mockResolvedValue(mockTLAConfig);
      vi.mocked(tlcRunner.runTLC).mockRejectedValue(new Error('Docker not running'));

      const result = await runCEGISLoop(mockSpec, 8);

      expect(result.success).toBe(false);
      expect(result.error).toContain('TLC execution failed');
      expect(result.error).toContain('Docker not running');
    });
  });

  describe('iteration history', () => {
    it('should track all iterations with correct data', async () => {
      vi.mocked(codeGenerator.generateCode).mockResolvedValue(mockGeneratedCode);
      vi.mocked(tlaGenerator.generateTLAModule).mockResolvedValue({ source: mockTLASpec } as any);
      vi.mocked(tlaGenerator.tlaModuleToString).mockReturnValue(mockTLASpec);
      vi.mocked(tlaGenerator.generateTLCConfig).mockResolvedValue(mockTLAConfig);

      const violationResult: TLCResult = {
        success: false,
        statesExplored: 10,
        invariantsChecked: [],
        violations: [{ invariantName: 'Test', message: 'Failed' }],
        output: 'Failed',
      };

      const successResult: TLCResult = {
        success: true,
        statesExplored: 50,
        invariantsChecked: ['Test'],
        output: 'Success',
      };

      vi.mocked(tlcRunner.runTLC)
        .mockResolvedValueOnce(violationResult)
        .mockResolvedValueOnce(violationResult)
        .mockResolvedValueOnce(successResult);

      const result = await runCEGISLoop(mockSpec, 8);

      expect(result.iterationHistory).toHaveLength(3);
      expect(result.iterationHistory[0].iteration).toBe(1);
      expect(result.iterationHistory[0].feedback).toBeUndefined();
      expect(result.iterationHistory[1].iteration).toBe(2);
      expect(result.iterationHistory[1].feedback).toBeDefined();
      expect(result.iterationHistory[2].iteration).toBe(3);
    });
  });
});
