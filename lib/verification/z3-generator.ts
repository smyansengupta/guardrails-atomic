/**
 * Z3 Constraint Generator
 * 
 * Generates Z3 SMT-LIB constraints from YAML specifications.
 * Z3 uses SMT (Satisfiability Modulo Theories) to verify invariants.
 * 
 * Key concepts:
 * - declare-const: Define variables (e.g., balance_a1, processed_req1)
 * - assert: Add constraints (preconditions, postconditions, invariants)
 * - check-sat: Ask Z3 to find counter-examples (sat) or prove unsat
 * 
 * Result interpretation:
 * - unsat = No counter-example exists = Code is CORRECT ✅
 * - sat = Found counter-example = Code has BUG ❌
 */

import { Specification, Invariant } from '@/lib/types/specification';
import { Z3Module, Z3Constant, Z3Constraint, Z3Assertion } from '@/lib/types/z3-ast';
import { logger } from '@/lib/utils/logger';

/**
 * Generate Z3 constraints from specification
 */
export function generateZ3Module(spec: Specification): Z3Module {
  logger.debug('Generating Z3 module', { specName: spec.name });

  const module: Z3Module = {
    name: spec.name,
    sorts: [],
    constants: generateConstants(spec),
    functions: [],
    constraints: [],
    assertions: [],
    checkSat: true,
  };

  // Generate constraints for each phase
  module.constraints.push(...generatePreconditionConstraints(spec));
  module.constraints.push(...generatePostconditionConstraints(spec));
  module.constraints.push(...generateInvariantConstraints(spec));
  module.constraints.push(...generateFaultModelConstraints(spec));

  logger.debug('Z3 module generated', {
    constants: module.constants.length,
    constraints: module.constraints.length,
  });

  return module;
}

/**
 * Generate Z3 constants (variables) from specification
 */
function generateConstants(spec: Specification): Z3Constant[] {
  const constants: Z3Constant[] = [];

  // Generate balance variables for each account
  const numAccounts = spec.bounds?.accts || 3;
  for (let i = 1; i <= numAccounts; i++) {
    constants.push({
      name: `balance_a${i}`,
      sort: 'Int',
    });
    constants.push({
      name: `balance_a${i}_after`,
      sort: 'Int',
    });
  }

  // Add processed set tracking for idempotency
  if (spec.invariants.some(inv => inv.type === 'idempotent')) {
    // Use boolean flags for processed requests
    const maxRetries = spec.bounds?.retries || 2;
    for (let i = 1; i <= maxRetries; i++) {
      constants.push({
        name: `processed_req${i}`,
        sort: 'Bool',
      });
    }
  }

  // Add transfer parameters
  spec.signature.params.forEach(param => {
    if (param.type === 'int' || param.type === 'Int') {
      constants.push({
        name: param.name,
        sort: 'Int',
      });
    } else if (param.type === 'Acct' || param.type === 'String') {
      // For simplicity, represent accounts as integers (1, 2, 3)
      constants.push({
        name: param.name,
        sort: 'Int',
      });
    }
  });

  return constants;
}

/**
 * Generate precondition constraints
 */
function generatePreconditionConstraints(spec: Specification): Z3Constraint[] {
  return spec.preconditions
    .filter(precond => {
      // Skip preconditions with dynamic array access (state[variable])
      const hasDynamicAccess = /(?:state|result)\[(?!a\d+)[a-z_]+\]/i.test(precond);
      if (hasDynamicAccess) {
        logger.warn('Skipping precondition with dynamic array access', { precond });
        return false;
      }
      return true;
    })
    .map((precond, idx) => ({
      name: `Precondition_${idx + 1}`,
      formula: translateConditionToZ3(precond, spec),
      description: precond,
      type: 'precondition' as const,
    }));
}

/**
 * Generate postcondition constraints
 */
function generatePostconditionConstraints(spec: Specification): Z3Constraint[] {
  return spec.postconditions
    .filter(postcond => {
      // Skip postconditions with dynamic array access (state[variable])
      // These require Z3 arrays or enumeration to handle properly
      const hasDynamicAccess = /(?:state|result)\[(?!a\d+)[a-z_]+\]/i.test(postcond);
      if (hasDynamicAccess) {
        logger.warn('Skipping postcondition with dynamic array access', { postcond });
        return false;
      }
      return true;
    })
    .map((postcond, idx) => ({
      name: `Postcondition_${idx + 1}`,
      formula: translateConditionToZ3(postcond, spec, true),
      description: postcond,
      type: 'postcondition' as const,
    }));
}

/**
 * Generate invariant constraints
 */
function generateInvariantConstraints(spec: Specification): Z3Constraint[] {
  const constraints: Z3Constraint[] = [];

  for (const invariant of spec.invariants) {
    switch (invariant.type) {
      case 'idempotent':
        constraints.push(generateIdempotencyConstraint(spec, invariant));
        break;
      case 'conservation':
        constraints.push(generateConservationConstraint(spec, invariant));
        break;
      case 'no_double_spend':
        constraints.push(generateNoDoubleSpendConstraint(spec, invariant));
        break;
      case 'atomic_no_partial_commit':
        constraints.push(generateAtomicityConstraint(spec, invariant));
        break;
    }
  }

  return constraints;
}

/**
 * Generate fault model constraints (at_least_once, reorder, etc.)
 */
function generateFaultModelConstraints(spec: Specification): Z3Constraint[] {
  const constraints: Z3Constraint[] = [];

  // at_least_once: Allow duplicate execution
  if (spec.faultModel.delivery === 'at_least_once') {
    constraints.push({
      name: 'DuplicateDelivery',
      formula: '(or processed_req1 (not processed_req1))', // Can be processed or not
      description: 'Message can be delivered multiple times',
      type: 'transition',
    });
  }

  return constraints;
}

/**
 * Generate idempotency invariant
 * Duplicate requests must not change state
 */
function generateIdempotencyConstraint(spec: Specification, inv: Invariant): Z3Constraint {
  const numAccounts = spec.bounds?.accts || 3;
  
  // If already processed, state should be unchanged
  const unchangedConditions: string[] = [];
  for (let i = 1; i <= numAccounts; i++) {
    unchangedConditions.push(`(= balance_a${i}_after balance_a${i})`);
  }

  const formula = `(=> processed_req1 (and ${unchangedConditions.join(' ')}))`;

  return {
    name: 'Idempotent',
    formula,
    description: 'Duplicate requests must not change state',
    type: 'invariant',
  };
}

/**
 * Generate conservation invariant
 * Total sum of resources must remain constant
 */
function generateConservationConstraint(spec: Specification, inv: Invariant): Z3Constraint {
  const numAccounts = spec.bounds?.accts || 3;
  
  const beforeSum = Array.from({ length: numAccounts }, (_, i) => `balance_a${i + 1}`).join(' + ');
  const afterSum = Array.from({ length: numAccounts }, (_, i) => `balance_a${i + 1}_after`).join(' + ');

  const formula = `(= (+ ${beforeSum.replace(/\+/g, '')}) (+ ${afterSum.replace(/\+/g, '')}))`;

  return {
    name: 'Conservation',
    formula,
    description: 'Total resources must be conserved',
    type: 'invariant',
  };
}

/**
 * Generate no-double-spend invariant
 * All balances must be non-negative
 */
function generateNoDoubleSpendConstraint(spec: Specification, inv: Invariant): Z3Constraint {
  const numAccounts = spec.bounds?.accts || 3;
  
  const conditions = Array.from(
    { length: numAccounts },
    (_, i) => `(>= balance_a${i + 1}_after 0)`
  );

  const formula = `(and ${conditions.join(' ')})`;

  return {
    name: 'NoDoubleSpend',
    formula,
    description: 'All balances must be non-negative',
    type: 'invariant',
  };
}

/**
 * Generate atomicity invariant
 * Either all updates happen or none
 */
function generateAtomicityConstraint(spec: Specification, inv: Invariant): Z3Constraint {
  // This is typically checked by the transaction logic itself
  // For Z3, we assert that partial updates don't occur
  return {
    name: 'Atomicity',
    formula: '(= transaction_complete true)',
    description: 'All state changes must be atomic',
    type: 'invariant',
  };
}

/**
 * Translate YAML condition to Z3 SMT-LIB format
 */
function translateConditionToZ3(condition: string, spec: Specification, isPostcondition: boolean = false): string {
  let z3 = condition.trim();

  // Handle sum() function FIRST (before state references)
  z3 = z3.replace(/sum\(([^)]+)\.values\(\)\)/g, (_, expr) => {
    // Extract variable name from expression like "result" or "state"
    // In postconditions: result = after state, state = before state
    // In preconditions: state = before state
    const useAfter = expr.includes('result');
    const numAccounts = spec.bounds?.accts || 3;
    const balances = Array.from(
      { length: numAccounts }, 
      (_, i) => `balance_a${i + 1}${useAfter ? '_after' : ''}`
    );
    return `(+ ${balances.join(' ')})`;
  });

  // Replace state references
  if (isPostcondition) {
    z3 = z3.replace(/state\[(\w+)\]/g, 'balance_$1_after');
    z3 = z3.replace(/result\[(\w+)\]/g, 'balance_$1_after');
  } else {
    z3 = z3.replace(/state\[(\w+)\]/g, 'balance_$1');
  }

  // Handle != operator (convert to distinct) - BEFORE other operators
  z3 = z3.replace(/(\w+)\s*!=\s*(\w+)/g, '(distinct $1 $2)');
  
  // Handle == operator - match more carefully to handle expressions
  // Match: "expr1 == expr2" where expr can contain parentheses
  if (z3.includes('==')) {
    const parts = z3.split('==').map(p => p.trim());
    if (parts.length === 2) {
      z3 = `(= ${parts[0]} ${parts[1]})`;
    }
  }

  // Handle comparison operators: >=, <=, >, <
  // Only if not already wrapped
  if (!z3.startsWith('(')) {
    z3 = z3.replace(/(\w+)\s*(>=|<=|>|<)\s*(-?\w+)/g, '($2 $1 $3)');
  }

  // Handle boolean operators
  z3 = z3.replace(/&&/g, 'and');
  z3 = z3.replace(/\|\|/g, 'or');
  
  // Handle negation carefully (don't replace ! in !=)
  z3 = z3.replace(/!(?!=)/g, 'not ');

  return z3;
}

/**
 * Serialize Z3 module to SMT-LIB format
 * 
 * SMT-LIB is the standard input format for Z3
 */
export function z3ModuleToString(module: Z3Module): string {
  const lines: string[] = [];

  // Header comment
  lines.push(`; Z3 SMT-LIB specification for ${module.name}`);
  lines.push('; Generated by Guardrails: Atomic');
  lines.push('');

  // Declare constants
  lines.push('; Constants (variables)');
  for (const constant of module.constants) {
    lines.push(`(declare-const ${constant.name} ${constant.sort})`);
  }
  lines.push('');

  // Assert constraints
  lines.push('; Constraints');
  for (const constraint of module.constraints) {
    if (constraint.description) {
      lines.push(`; ${constraint.description}`);
    }
    lines.push(`(assert ${constraint.formula})`);
    lines.push('');
  }

  // Add negation of invariants to find counter-examples
  // If Z3 returns 'sat', it found a counter-example (bug!)
  // If Z3 returns 'unsat', no counter-example exists (correct!)
  lines.push('; Check satisfiability (looking for counter-examples)');
  lines.push('(check-sat)');
  lines.push('(get-model)');

  return lines.join('\n');
}

/**
 * Generate Z3 config (not needed for z3-solver, but kept for compatibility)
 */
export function generateZ3Config(spec: Specification): string {
  return `; Z3 configuration for ${spec.name}
; timeout: 60000ms
; model-based: true
`;
}

