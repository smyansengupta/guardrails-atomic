import { describe, it, expect } from 'vitest';
import {
  SpecificationError,
  VerificationError,
  TLCExecutionError,
  CodeGenerationError,
  NLToYAMLError,
} from '@/lib/utils/errors';

describe('Error Classes', () => {
  describe('SpecificationError', () => {
    it('should create error with correct name', () => {
      const error = new SpecificationError('Test message');

      expect(error).toBeInstanceOf(Error);
      expect(error.name).toBe('SpecificationError');
      expect(error.message).toBe('Test message');
    });

    it('should be catchable as Error', () => {
      try {
        throw new SpecificationError('Test error');
      } catch (error) {
        expect(error).toBeInstanceOf(Error);
        expect(error).toBeInstanceOf(SpecificationError);
      }
    });

    it('should have stack trace', () => {
      const error = new SpecificationError('Test message');

      expect(error.stack).toBeDefined();
      expect(error.stack).toContain('SpecificationError');
    });

    it('should preserve error message with special characters', () => {
      const message = 'Error with\nnewlines and "quotes"';
      const error = new SpecificationError(message);

      expect(error.message).toBe(message);
    });
  });

  describe('VerificationError', () => {
    it('should create error with correct name', () => {
      const error = new VerificationError('Verification failed');

      expect(error).toBeInstanceOf(Error);
      expect(error.name).toBe('VerificationError');
      expect(error.message).toBe('Verification failed');
    });

    it('should be distinguishable from SpecificationError', () => {
      const specError = new SpecificationError('Spec error');
      const verifyError = new VerificationError('Verify error');

      expect(specError).not.toBeInstanceOf(VerificationError);
      expect(verifyError).not.toBeInstanceOf(SpecificationError);
    });
  });

  describe('TLCExecutionError', () => {
    it('should create error with correct name', () => {
      const error = new TLCExecutionError('TLC failed');

      expect(error).toBeInstanceOf(Error);
      expect(error.name).toBe('TLCExecutionError');
      expect(error.message).toBe('TLC failed');
    });

    it('should store optional output parameter', () => {
      const output = 'TLC output:\nState 1: ...\nState 2: ...';
      const error = new TLCExecutionError('TLC failed', output);

      expect(error.output).toBe(output);
    });

    it('should work without output parameter', () => {
      const error = new TLCExecutionError('TLC failed');

      expect(error.output).toBeUndefined();
    });

    it('should preserve output with special characters', () => {
      const output = 'Output\twith\ttabs\nand\nnewlines';
      const error = new TLCExecutionError('Failed', output);

      expect(error.output).toBe(output);
    });
  });

  describe('CodeGenerationError', () => {
    it('should create error with correct name', () => {
      const error = new CodeGenerationError('Code generation failed');

      expect(error).toBeInstanceOf(Error);
      expect(error.name).toBe('CodeGenerationError');
      expect(error.message).toBe('Code generation failed');
    });

    it('should be catchable in try-catch', () => {
      let caught = false;

      try {
        throw new CodeGenerationError('LLM timeout');
      } catch (error) {
        if (error instanceof CodeGenerationError) {
          caught = true;
          expect(error.message).toBe('LLM timeout');
        }
      }

      expect(caught).toBe(true);
    });
  });

  describe('NLToYAMLError', () => {
    it('should create error with correct name', () => {
      const error = new NLToYAMLError('NL to YAML conversion failed');

      expect(error).toBeInstanceOf(Error);
      expect(error.name).toBe('NLToYAMLError');
      expect(error.message).toBe('NL to YAML conversion failed');
    });

    it('should be distinguishable from CodeGenerationError', () => {
      const nlError = new NLToYAMLError('NL error');
      const codeError = new CodeGenerationError('Code error');

      expect(nlError).not.toBeInstanceOf(CodeGenerationError);
      expect(codeError).not.toBeInstanceOf(NLToYAMLError);
    });
  });

  describe('Error inheritance and type checking', () => {
    it('should all inherit from Error', () => {
      const errors = [
        new SpecificationError('msg'),
        new VerificationError('msg'),
        new TLCExecutionError('msg'),
        new CodeGenerationError('msg'),
        new NLToYAMLError('msg'),
      ];

      errors.forEach((error) => {
        expect(error).toBeInstanceOf(Error);
      });
    });

    it('should be type-checkable with instanceof', () => {
      const error: Error = new SpecificationError('Test');

      if (error instanceof SpecificationError) {
        expect(error.name).toBe('SpecificationError');
      } else {
        throw new Error('instanceof check failed');
      }
    });

    it('should work in switch-like error handling', () => {
      const handleError = (error: Error): string => {
        if (error instanceof SpecificationError) return 'spec';
        if (error instanceof VerificationError) return 'verify';
        if (error instanceof TLCExecutionError) return 'tlc';
        if (error instanceof CodeGenerationError) return 'code';
        if (error instanceof NLToYAMLError) return 'nl';
        return 'unknown';
      };

      expect(handleError(new SpecificationError('msg'))).toBe('spec');
      expect(handleError(new VerificationError('msg'))).toBe('verify');
      expect(handleError(new TLCExecutionError('msg'))).toBe('tlc');
      expect(handleError(new CodeGenerationError('msg'))).toBe('code');
      expect(handleError(new NLToYAMLError('msg'))).toBe('nl');
      expect(handleError(new Error('msg'))).toBe('unknown');
    });
  });

  describe('Error serialization', () => {
    it('should serialize to JSON', () => {
      const error = new SpecificationError('Test error');
      const serialized = JSON.stringify(error);

      expect(serialized).toContain('SpecificationError');
    });

    it('should preserve error info when thrown and caught', () => {
      let caughtError: Error | null = null;

      try {
        throw new SpecificationError('Original message');
      } catch (error) {
        caughtError = error as Error;
      }

      expect(caughtError).not.toBeNull();
      expect(caughtError!.message).toBe('Original message');
      expect(caughtError).toBeInstanceOf(SpecificationError);
    });

    it('should work with Error.prototype methods', () => {
      const error = new SpecificationError('Test');

      expect(error.toString()).toContain('SpecificationError');
      expect(error.toString()).toContain('Test');
    });
  });

  describe('Edge cases', () => {
    it('should handle empty error messages', () => {
      const error = new SpecificationError('');

      expect(error.message).toBe('');
      expect(error.name).toBe('SpecificationError');
    });

    it('should handle very long error messages', () => {
      const longMessage = 'Error: ' + 'a'.repeat(10000);
      const error = new SpecificationError(longMessage);

      expect(error.message).toBe(longMessage);
      expect(error.message.length).toBe(longMessage.length);
    });

    it('should handle unicode in error messages', () => {
      const message = '�: Invalid spec =�';
      const error = new SpecificationError(message);

      expect(error.message).toBe(message);
    });

    it('should handle TLCExecutionError with empty output', () => {
      const error = new TLCExecutionError('Failed', '');

      expect(error.output).toBe('');
    });
  });
});
