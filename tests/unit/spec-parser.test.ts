import { describe, it, expect } from 'vitest';
import { parseSpec } from '@/lib/core/spec-parser';
import { SpecificationError } from '@/lib/utils/errors';

describe('spec-parser', () => {
  describe('Valid YAML parsing', () => {
    it('should parse valid transfer spec', () => {
      const yaml = `
name: transfer_atomic
signature:
  params:
    - name: state
      type: Map<Acct,int>
    - name: from
      type: Acct
    - name: to
      type: Acct
    - name: amt
      type: int
    - name: req_id
      type: UUID
  returnType: Map<Acct,int>
preconditions:
  - amt >= 0
postconditions:
  - sum(result.values()) == sum(state.values())
invariants:
  - type: idempotent
faultModel:
  delivery: at_least_once
  reorder: true
  crash_restart: true
bounds:
  accts: 3
`;

      const spec = parseSpec(yaml);

      expect(spec.name).toBe('transfer_atomic');
      expect(spec.signature.params).toHaveLength(5);
      expect(spec.signature.returnType).toBe('Map<Acct,int>');
      expect(spec.preconditions).toHaveLength(1);
      expect(spec.postconditions).toHaveLength(1);
      expect(spec.invariants).toHaveLength(1);
      expect(spec.invariants[0].type).toBe('idempotent');
      expect(spec.faultModel.delivery).toBe('at_least_once');
      expect(spec.faultModel.reorder).toBe(true);
      expect(spec.faultModel.crash_restart).toBe(true);
      expect(spec.bounds.accts).toBe(3);
    });

    it('should parse spec with multiple invariants', () => {
      const yaml = `
name: multi_invariant
signature:
  params:
    - name: data
      type: string
  returnType: boolean
preconditions: []
postconditions: []
invariants:
  - type: idempotent
  - type: conservation
  - type: no_double_spend
faultModel:
  delivery: exactly_once
  reorder: false
  crash_restart: false
bounds:
  accts: 2
`;

      const spec = parseSpec(yaml);

      expect(spec.invariants).toHaveLength(3);
      expect(spec.invariants[0].type).toBe('idempotent');
      expect(spec.invariants[1].type).toBe('conservation');
      expect(spec.invariants[2].type).toBe('no_double_spend');
    });

    it('should parse spec with optional invariant description', () => {
      const yaml = `
name: with_description
signature:
  params:
    - name: value
      type: int
  returnType: void
preconditions: []
postconditions: []
invariants:
  - type: idempotent
    description: Ensures repeated calls have no additional effect
faultModel:
  delivery: at_most_once
  reorder: true
  crash_restart: false
bounds:
  accts: 1
`;

      const spec = parseSpec(yaml);

      expect(spec.invariants[0].description).toBe('Ensures repeated calls have no additional effect');
    });

    it('should parse spec with all fault model options', () => {
      const yaml = `
name: all_faults
signature:
  params: []
  returnType: void
preconditions: []
postconditions: []
invariants: []
faultModel:
  delivery: at_least_once
  reorder: true
  crash_restart: true
  network_partition: true
bounds:
  accts: 5
  retries: 3
  messages: 10
  depth: 7
`;

      const spec = parseSpec(yaml);

      expect(spec.faultModel.network_partition).toBe(true);
      expect(spec.bounds.retries).toBe(3);
      expect(spec.bounds.messages).toBe(10);
      expect(spec.bounds.depth).toBe(7);
    });
  });

  describe('Invalid YAML handling', () => {
    it('should throw on invalid YAML syntax', () => {
      const invalidYaml = 'name: test\ninvalid: [unclosed';

      expect(() => parseSpec(invalidYaml)).toThrow(SpecificationError);
      expect(() => parseSpec(invalidYaml)).toThrow(/YAML parsing failed/);
    });

    it('should throw on empty YAML', () => {
      expect(() => parseSpec('')).toThrow(SpecificationError);
      expect(() => parseSpec('')).toThrow(/empty or invalid/);
    });

    it('should throw on null YAML', () => {
      expect(() => parseSpec('null')).toThrow(SpecificationError);
    });
  });

  describe('Schema validation', () => {
    it('should throw on missing required fields', () => {
      const incompleteYaml = 'name: test';

      expect(() => parseSpec(incompleteYaml)).toThrow(SpecificationError);
      expect(() => parseSpec(incompleteYaml)).toThrow(/Validation failed/);
    });

    it('should throw on missing name field', () => {
      const yaml = `
signature:
  params: []
  returnType: void
preconditions: []
postconditions: []
invariants: []
faultModel:
  delivery: at_least_once
  reorder: false
  crash_restart: false
bounds:
  accts: 1
`;

      expect(() => parseSpec(yaml)).toThrow(SpecificationError);
      expect(() => parseSpec(yaml)).toThrow(/name/);
    });

    it('should throw on invalid invariant type', () => {
      const yaml = `
name: invalid_invariant
signature:
  params: []
  returnType: void
preconditions: []
postconditions: []
invariants:
  - type: invalid_type
faultModel:
  delivery: at_least_once
  reorder: false
  crash_restart: false
bounds:
  accts: 1
`;

      expect(() => parseSpec(yaml)).toThrow(SpecificationError);
    });

    it('should throw on invalid delivery type', () => {
      const yaml = `
name: invalid_delivery
signature:
  params: []
  returnType: void
preconditions: []
postconditions: []
invariants: []
faultModel:
  delivery: invalid_delivery
  reorder: false
  crash_restart: false
bounds:
  accts: 1
`;

      expect(() => parseSpec(yaml)).toThrow(SpecificationError);
    });

    it('should throw on missing signature', () => {
      const yaml = `
name: no_signature
preconditions: []
postconditions: []
invariants: []
faultModel:
  delivery: at_least_once
  reorder: false
  crash_restart: false
bounds:
  accts: 1
`;

      expect(() => parseSpec(yaml)).toThrow(SpecificationError);
      expect(() => parseSpec(yaml)).toThrow(/signature/);
    });

    it('should throw on invalid param structure', () => {
      const yaml = `
name: bad_params
signature:
  params:
    - invalid_param_structure
  returnType: void
preconditions: []
postconditions: []
invariants: []
faultModel:
  delivery: at_least_once
  reorder: false
  crash_restart: false
bounds:
  accts: 1
`;

      expect(() => parseSpec(yaml)).toThrow(SpecificationError);
    });

    it('should throw on non-boolean reorder field', () => {
      const yaml = `
name: bad_reorder
signature:
  params: []
  returnType: void
preconditions: []
postconditions: []
invariants: []
faultModel:
  delivery: at_least_once
  reorder: "not_a_boolean"
  crash_restart: false
bounds:
  accts: 1
`;

      expect(() => parseSpec(yaml)).toThrow(SpecificationError);
    });
  });

  describe('Edge cases', () => {
    it('should handle empty arrays', () => {
      const yaml = `
name: empty_arrays
signature:
  params: []
  returnType: void
preconditions: []
postconditions: []
invariants: []
faultModel:
  delivery: exactly_once
  reorder: false
  crash_restart: false
bounds:
  accts: 1
`;

      const spec = parseSpec(yaml);

      expect(spec.signature.params).toHaveLength(0);
      expect(spec.preconditions).toHaveLength(0);
      expect(spec.postconditions).toHaveLength(0);
      expect(spec.invariants).toHaveLength(0);
    });

    it('should handle complex nested types in params', () => {
      const yaml = `
name: complex_types
signature:
  params:
    - name: nested
      type: Map<string, Array<Map<int, bool>>>
  returnType: Option<Result<T, E>>
preconditions: []
postconditions: []
invariants: []
faultModel:
  delivery: at_least_once
  reorder: false
  crash_restart: false
bounds:
  accts: 1
`;

      const spec = parseSpec(yaml);

      expect(spec.signature.params[0].type).toBe('Map<string, Array<Map<int, bool>>>');
      expect(spec.signature.returnType).toBe('Option<Result<T, E>>');
    });

    it('should preserve whitespace in preconditions and postconditions', () => {
      const yaml = `
name: whitespace_test
signature:
  params: []
  returnType: void
preconditions:
  - "x > 0 && y < 100"
  - "state.balance >= amount"
postconditions:
  - "result.success == true"
invariants: []
faultModel:
  delivery: at_least_once
  reorder: false
  crash_restart: false
bounds:
  accts: 1
`;

      const spec = parseSpec(yaml);

      expect(spec.preconditions[0]).toBe('x > 0 && y < 100');
      expect(spec.preconditions[1]).toBe('state.balance >= amount');
      expect(spec.postconditions[0]).toBe('result.success == true');
    });
  });
});
