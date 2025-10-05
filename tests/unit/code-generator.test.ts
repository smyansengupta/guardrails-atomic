import { describe, it, expect, vi, beforeEach, Mock } from 'vitest';
import { generateCode, formatSignature, formatPreconditions, formatPostconditions, formatInvariants, extractCodeFromMarkdown, parseFeedback } from '@/lib/core/code-generator';
import { Specification, FunctionSignature, Invariant } from '@/lib/types/specification';
import { generateWithOpenRouter } from '@/lib/services/openrouter.service';
import { CodeGenerationError } from '@/lib/utils/errors';
import { readFile } from 'fs/promises';

// Mock dependencies
vi.mock('@/lib/services/openrouter.service');
vi.mock('fs/promises');

describe('code-generator', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('formatSignature', () => {
    it('should format function signature with multiple params', () => {
      const signature: FunctionSignature = {
        params: [
          { name: 'state', type: 'Map<Acct,int>' },
          { name: 'from', type: 'Acct' },
          { name: 'to', type: 'Acct' },
          { name: 'amt', type: 'int' },
        ],
        returnType: 'Map<Acct,int>',
      };

      const result = formatSignature(signature, 'transfer');
      expect(result).toBe('function transfer(state: Map<Acct,int>, from: Acct, to: Acct, amt: int): Map<Acct,int>');
    });

    it('should format function signature with no params', () => {
      const signature: FunctionSignature = {
        params: [],
        returnType: 'void',
      };

      const result = formatSignature(signature, 'initialize');
      expect(result).toBe('function initialize(): void');
    });

    it('should format function signature with one param', () => {
      const signature: FunctionSignature = {
        params: [{ name: 'id', type: 'string' }],
        returnType: 'boolean',
      };

      const result = formatSignature(signature, 'exists');
      expect(result).toBe('function exists(id: string): boolean');
    });
  });

  describe('formatPreconditions', () => {
    it('should format preconditions as bulleted list', () => {
      const preconditions = ['amt >= 0', 'from != to', 'state[from] >= amt'];
      const result = formatPreconditions(preconditions);
      expect(result).toBe('- amt >= 0\n- from != to\n- state[from] >= amt');
    });

    it('should handle empty preconditions', () => {
      const result = formatPreconditions([]);
      expect(result).toBe('(none)');
    });

    it('should handle single precondition', () => {
      const result = formatPreconditions(['x > 0']);
      expect(result).toBe('- x > 0');
    });
  });

  describe('formatPostconditions', () => {
    it('should format postconditions as bulleted list', () => {
      const postconditions = [
        'sum(result.values()) == sum(state.values())',
        'result[from] == state[from] - amt',
      ];
      const result = formatPostconditions(postconditions);
      expect(result).toBe('- sum(result.values()) == sum(state.values())\n- result[from] == state[from] - amt');
    });

    it('should handle empty postconditions', () => {
      const result = formatPostconditions([]);
      expect(result).toBe('(none)');
    });
  });

  describe('formatInvariants', () => {
    it('should format invariants with descriptions', () => {
      const invariants: Invariant[] = [
        { type: 'idempotent', params: { key: 'req_id' } },
        { type: 'conservation' },
      ];

      const result = formatInvariants(invariants);
      expect(result).toContain('idempotent');
      expect(result).toContain('{"key":"req_id"}');
      expect(result).toContain('Repeated execution with same request ID has no additional effect');
      expect(result).toContain('conservation');
      expect(result).toContain('Total sum of resources remains constant');
    });

    it('should handle empty invariants', () => {
      const result = formatInvariants([]);
      expect(result).toBe('(none)');
    });

    it('should format all invariant types', () => {
      const invariants: Invariant[] = [
        { type: 'idempotent' },
        { type: 'no_double_spend' },
        { type: 'atomic_no_partial_commit' },
        { type: 'conservation' },
      ];

      const result = formatInvariants(invariants);
      expect(result).toContain('idempotent');
      expect(result).toContain('no_double_spend');
      expect(result).toContain('atomic_no_partial_commit');
      expect(result).toContain('conservation');
    });
  });

  describe('extractCodeFromMarkdown', () => {
    it('should extract code from typescript markdown block', () => {
      const response = '```typescript\nfunction foo() {}\n```';
      const result = extractCodeFromMarkdown(response);
      expect(result).toBe('function foo() {}');
    });

    it('should extract code from ts markdown block', () => {
      const response = '```ts\nconst x = 5;\n```';
      const result = extractCodeFromMarkdown(response);
      expect(result).toBe('const x = 5;');
    });

    it('should extract code from generic markdown block', () => {
      const response = '```\nlet y = 10;\n```';
      const result = extractCodeFromMarkdown(response);
      expect(result).toBe('let y = 10;');
    });

    it('should return trimmed response if no markdown wrapper', () => {
      const response = '  function bar() {}  ';
      const result = extractCodeFromMarkdown(response);
      expect(result).toBe('function bar() {}');
    });

    it('should handle multiline code blocks', () => {
      const response = `\`\`\`typescript
function transfer(state, from, to, amt) {
  if (amt < 0) return;
  state[from] -= amt;
  state[to] += amt;
}
\`\`\``;
      const result = extractCodeFromMarkdown(response);
      expect(result).toContain('function transfer');
      expect(result).toContain('state[from] -= amt');
    });
  });

  describe('parseFeedback', () => {
    it('should parse complete feedback with all sections', () => {
      const feedback = `ORIGINAL CODE:
function transfer() { /* buggy code */ }

VIOLATION: Idempotent invariant failed

EXECUTION TRACE:
1. Init - State: balance=100
2. Transfer - State: balance=50
3. DuplicateTransfer - State: balance=0

ISSUE: Duplicate request was not detected

FIX: Add idempotency check using req_id tracking`;

      const result = parseFeedback(feedback);
      expect(result.code).toContain('function transfer');
      expect(result.violation).toContain('Idempotent');
      expect(result.violation).toContain('Duplicate request');
      expect(result.trace).toContain('Init');
      expect(result.trace).toContain('DuplicateTransfer');
      expect(result.suggestion).toContain('idempotency check');
    });

    it('should handle feedback without original code', () => {
      const feedback = `VIOLATION: Conservation invariant failed

EXECUTION TRACE:
1. Init

ISSUE: Sum not preserved

FIX: Check balance updates`;

      const result = parseFeedback(feedback);
      expect(result.code).toBe('// Previous code not available');
      expect(result.violation).toContain('Conservation');
      expect(result.trace).toContain('Init');
      expect(result.suggestion).toContain('balance updates');
    });

    it('should handle minimal feedback', () => {
      const feedback = 'VIOLATION: TypeOK';
      const result = parseFeedback(feedback);
      expect(result.violation).toContain('TypeOK');
      expect(result.trace).toBe('No trace available');
      expect(result.suggestion).toBeTruthy();
    });
  });

  describe('generateCode', () => {
    const mockSpec: Specification = {
      name: 'transfer',
      signature: {
        params: [
          { name: 'state', type: 'Map<Acct,int>' },
          { name: 'amt', type: 'int' },
        ],
        returnType: 'Map<Acct,int>',
      },
      preconditions: ['amt >= 0'],
      postconditions: ['result != null'],
      invariants: [{ type: 'idempotent' }],
      faultModel: {
        delivery: 'at_least_once',
        reorder: true,
        crash_restart: false,
      },
      bounds: {
        accts: 3,
      },
    };

    beforeEach(() => {
      (readFile as Mock).mockResolvedValue('Template: {{name}} {{signature}}');
      (generateWithOpenRouter as Mock).mockResolvedValue('```typescript\nfunction test() {}\n```');
    });

    it('should generate code from specification', async () => {
      const result = await generateCode(mockSpec);
      expect(result).toBe('function test() {}');
      expect(readFile).toHaveBeenCalledWith(
        expect.stringContaining('code-generation.txt'),
        'utf-8'
      );
      expect(generateWithOpenRouter).toHaveBeenCalled();
    });

    it('should use repair template when feedback provided', async () => {
      const feedback = `ORIGINAL CODE:
function old() {}

VIOLATION: Bug found

EXECUTION TRACE:
Step 1

ISSUE: Problem

FIX: Solution`;

      await generateCode(mockSpec, feedback);
      expect(readFile).toHaveBeenCalledWith(
        expect.stringContaining('code-repair.txt'),
        'utf-8'
      );
    });

    it('should throw CodeGenerationError if template file not found', async () => {
      (readFile as Mock).mockRejectedValue(new Error('ENOENT'));

      await expect(generateCode(mockSpec)).rejects.toThrow(CodeGenerationError);
    });

    it('should throw CodeGenerationError if LLM returns empty code', async () => {
      (generateWithOpenRouter as Mock).mockResolvedValue('   ');

      await expect(generateCode(mockSpec)).rejects.toThrow(CodeGenerationError);
      await expect(generateCode(mockSpec)).rejects.toThrow('empty code');
    });

    it('should throw CodeGenerationError if OpenRouter fails', async () => {
      (generateWithOpenRouter as Mock).mockRejectedValue(new Error('API Error'));

      await expect(generateCode(mockSpec)).rejects.toThrow(CodeGenerationError);
    });

    it('should handle code without markdown wrapper', async () => {
      (generateWithOpenRouter as Mock).mockResolvedValue('function plain() {}');

      const result = await generateCode(mockSpec);
      expect(result).toBe('function plain() {}');
    });

    it('should replace all template placeholders for initial generation', async () => {
      const template = `NAME: {{name}}
SIGNATURE: {{signature}}
PRECONDITIONS:
{{preconditions}}
POSTCONDITIONS:
{{postconditions}}
INVARIANTS:
{{invariants}}
DELIVERY: {{delivery}}
REORDER: {{reorder}}
CRASH: {{crash_restart}}`;

      (readFile as Mock).mockResolvedValue(template);
      (generateWithOpenRouter as Mock).mockImplementation((prompt: string) => {
        // Verify all placeholders were replaced
        expect(prompt).not.toContain('{{');
        expect(prompt).toContain('transfer');
        expect(prompt).toContain('function transfer');
        expect(prompt).toContain('amt >= 0');
        expect(prompt).toContain('at_least_once');
        expect(prompt).toContain('true');
        expect(prompt).toContain('false');
        return Promise.resolve('```typescript\ngenerated\n```');
      });

      await generateCode(mockSpec);
    });
  });
});
