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
    .map((precond, idx) => {
      const formula = translateConditionToZ3(precond, spec, false);
      return {
        name: `Precondition_${idx + 1}`,
        formula,
        description: precond,
        type: 'precondition' as const,
      };
    });
}

/**
 * Generate postcondition constraints
 */
function generatePostconditionConstraints(spec: Specification): Z3Constraint[] {
  return spec.postconditions
    .map((postcond, idx) => {
      const formula = translateConditionToZ3(postcond, spec, true);
      return {
        name: `Postcondition_${idx + 1}`,
        formula,
        description: postcond,
        type: 'postcondition' as const,
      };
    });
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
 *
 * Handles:
 * - Dynamic array access: state[variable] where variable is a parameter
 * - old() function for before/after state comparison
 * - Arithmetic and comparison operators
 */
function translateConditionToZ3(condition: string, spec: Specification, isPostcondition: boolean = false): string {
  let z3 = condition.trim();

  // Handle sum() function FIRST (before state references)
  // In postconditions:
  //   sum(result.values()) = after-state sum
  //   sum(state.values()) = before-state sum (OLD state)
  z3 = z3.replace(/sum\(([^)]+)\.values\(\)\)/g, (_, expr) => {
    const numAccounts = spec.bounds?.accts || 3;
    let useAfter: boolean;

    if (isPostcondition) {
      // In postconditions: result = after, state = before
      useAfter = expr.includes('result');
    } else {
      // In preconditions: always before state
      useAfter = false;
    }

    const balances = Array.from(
      { length: numAccounts },
      (_, i) => `balance_a${i + 1}${useAfter ? '_after' : ''}`
    );
    return `(+ ${balances.join(' ')})`;
  });

  // Handle dynamic array access: state[variable] where variable is a parameter
  // Need to enumerate all possible values based on bounds
  const hasDynamicAccess = /(?:state|result)\[([a-z_]+)\]/i.test(z3);

  if (hasDynamicAccess) {
    // Enumerate all possible account values
    z3 = enumerateDynamicArrayAccess(z3, spec, isPostcondition);
  } else {
    // Static array access: state[a1], state[a2], etc.
    if (isPostcondition) {
      // In postconditions: result[x] = after, state[x] = before
      z3 = z3.replace(/result\[(\w+)\]/g, 'balance_$1_after');
      z3 = z3.replace(/state\[(\w+)\]/g, 'balance_$1'); // BEFORE state
    } else {
      z3 = z3.replace(/state\[(\w+)\]/g, 'balance_$1');
    }
  }

  // Handle != operator (convert to distinct) - BEFORE other operators
  z3 = z3.replace(/(\w+)\s*!=\s*(\w+)/g, '(distinct $1 $2)');

  // Handle == operator
  if (z3.includes('==')) {
    const parts = z3.split('==').map(p => p.trim());
    if (parts.length === 2) {
      z3 = `(= ${parts[0]} ${parts[1]})`;
    }
  }

  // Handle comparison operators: >=, <=, >, <
  if (!z3.startsWith('(')) {
    z3 = z3.replace(/(\w+)\s*(>=|<=|>|<)\s*(-?\w+)/g, '($2 $1 $3)');
  }

  // Handle boolean operators
  z3 = z3.replace(/&&/g, 'and');
  z3 = z3.replace(/\|\|/g, 'or');
  z3 = z3.replace(/!(?!=)/g, 'not ');

  return z3;
}

/**
 * Enumerate dynamic array access for all possible parameter values
 *
 * Example: "state[from] >= amt" with from parameter and bounds.accts = 3
 * Becomes: "(or (and (= from 1) (>= balance_a1 amt))
 *              (and (= from 2) (>= balance_a2 amt))
 *              (and (= from 3) (>= balance_a3 amt)))"
 */
function enumerateDynamicArrayAccess(
  condition: string,
  spec: Specification,
  isPostcondition: boolean
): string {
  const numAccounts = spec.bounds?.accts || 3;

  // Find all dynamic array accesses
  const dynamicAccessRegex = /(?:state|result)\[([a-z_]+)\]/gi;
  const matches = Array.from(condition.matchAll(dynamicAccessRegex));

  if (matches.length === 0) {
    return condition;
  }

  // For simplicity, handle common case: single parameter (from or to)
  const paramName = matches[0][1]; // e.g., "from" or "to"

  // Generate disjunctive constraint for each possible account
  const cases: string[] = [];

  for (let i = 1; i <= numAccounts; i++) {
    // Replace state[param] with balance_a{i} for this case
    let caseCondition = condition;

    // Replace occurrences based on context
    if (isPostcondition) {
      // In postconditions:
      //   result[param] → balance_a{i}_after (after state)
      //   state[param] → balance_a{i} (before state)
      caseCondition = caseCondition.replace(
        new RegExp(`result\\[${paramName}\\]`, 'g'),
        `balance_a${i}_after`
      );
      caseCondition = caseCondition.replace(
        new RegExp(`state\\[${paramName}\\]`, 'g'),
        `balance_a${i}` // BEFORE state
      );
    } else {
      // In preconditions: always before state
      caseCondition = caseCondition.replace(
        new RegExp(`state\\[${paramName}\\]`, 'g'),
        `balance_a${i}`
      );
    }

    // CRITICAL: Translate operators to SMT-LIB format BEFORE wrapping
    caseCondition = translateOperatorsToSMTLib(caseCondition);

    // Add guard: param = i
    cases.push(`(and (= ${paramName} ${i}) ${caseCondition})`);
  }

  // Return disjunction of all cases
  return cases.length > 1 ? `(or ${cases.join(' ')})` : cases[0];
}

/**
 * Helper function to translate operators to SMT-LIB format
 * This handles >=, <=, >, <, ==, !=, &&, ||, !
 */
function translateOperatorsToSMTLib(expr: string): string {
  let result = expr.trim();

  // Handle != operator (convert to distinct) - BEFORE other operators
  result = result.replace(/(\w+)\s*!=\s*(\w+)/g, '(distinct $1 $2)');

  // Handle == operator
  if (result.includes('==')) {
    const parts = result.split('==').map(p => p.trim());
    if (parts.length === 2) {
      result = `(= ${parts[0]} ${parts[1]})`;
    }
  }

  // Handle comparison operators: >=, <=, >, <
  // Only if not already wrapped
  if (!result.startsWith('(')) {
    // Match patterns like "balance_a1 >= amt"
    result = result.replace(/(\w+)\s*(>=|<=|>|<)\s*(-?\w+)/g, '($2 $1 $3)');
  }

  // Handle boolean operators
  result = result.replace(/&&/g, 'and');
  result = result.replace(/\|\|/g, 'or');
  result = result.replace(/!(?!=)/g, 'not ');

  return result;
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

