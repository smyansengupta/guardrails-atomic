/**
 * Z3 SMT Solver Runner
 * 
 * Executes Z3 solver using the z3-solver npm package.
 * 
 * Key concepts:
 * - sat: Z3 found a model that satisfies all constraints (counter-example found = BUG!)
 * - unsat: No model exists that satisfies constraints (code is CORRECT!)
 * - unknown: Z3 couldn't decide (timeout, too complex)
 * 
 * This is the OPPOSITE of what you might expect:
 * - We WANT unsat (no bugs found)
 * - We DON'T WANT sat (bug found)
 */

import { init } from 'z3-solver';
import { Z3Result, Z3Model, Z3CounterExample, Z3Value } from '@/lib/types/verification';
import { logger } from '@/lib/utils/logger';
import { VerificationError } from '@/lib/utils/errors';

/**
 * Run Z3 solver on SMT-LIB constraints
 * 
 * @param smtLib - SMT-LIB format constraints
 * @param config - Optional config (timeout, etc.)
 * @returns Z3Result with sat/unsat status and model if counter-example found
 */
export async function runZ3(
  smtLib: string,
  config?: { timeout?: number }
): Promise<Z3Result> {
  const startTime = Date.now();
  const timeout = config?.timeout || 60000; // 60 seconds default

  logger.info('Running Z3 solver');
  logger.debug('SMT-LIB input', { length: smtLib.length, timeout });

  try {
    // Initialize Z3
    // Note: z3-solver looks for WASM files in specific locations
    // We copy them via scripts to ensure they're accessible
    logger.debug('Initializing Z3 solver...');
    
    const { Context } = await init();
    const ctx = Context('main');
    const solver = new ctx.Solver();
    
    logger.debug('Z3 solver initialized successfully');

    // Set timeout
    solver.set('timeout', timeout);

    // Parse and execute SMT-LIB commands
    const result = await executeSMTLib(ctx, solver, smtLib);
    
    const duration = Date.now() - startTime;
    logger.info('Z3 completed', { 
      result: result.result, 
      duration: `${duration}ms` 
    });

    return {
      ...result,
      duration,
    };

  } catch (error) {
    const duration = Date.now() - startTime;
    logger.error('Z3 execution failed', { error, duration });
    
    throw new VerificationError(
      `Z3 execution failed: ${error instanceof Error ? error.message : String(error)}`
    );
  }
}

/**
 * Execute SMT-LIB commands using z3-solver API
 */
async function executeSMTLib(
  ctx: any,
  solver: any,
  smtLib: string
): Promise<Z3Result> {
  const lines = smtLib.split('\n');
  const constraintsChecked: string[] = [];
  const declarations: Map<string, any> = new Map();
  
  // Store ctx in declarations for recursive use
  declarations.set('__ctx__', ctx);

  for (const line of lines) {
    const trimmed = line.trim();
    
    // Skip comments and empty lines
    if (!trimmed || trimmed.startsWith(';')) {
      continue;
    }

    try {
      // Parse declare-const
      if (trimmed.startsWith('(declare-const')) {
        const match = trimmed.match(/\(declare-const\s+(\w+)\s+(\w+)\)/);
        if (match) {
          const [, varName, sort] = match;
          
          let variable;
          if (sort === 'Int') {
            variable = ctx.Int.const(varName);
          } else if (sort === 'Bool') {
            variable = ctx.Bool.const(varName);
          } else {
            logger.warn(`Unsupported sort: ${sort}`);
            continue;
          }
          
          declarations.set(varName, variable);
          logger.debug('Declared variable', { varName, sort });
        }
      }
      
      // Parse assert
      else if (trimmed.startsWith('(assert')) {
        const formula = trimmed.slice(8, -1).trim(); // Remove "(assert " and ")"
        
        // Translate formula to Z3 expression
        const z3Expr = translateFormulaToZ3(formula, declarations, ctx);
        if (z3Expr) {
          solver.add(z3Expr);
          constraintsChecked.push(formula);
          logger.debug('Added constraint', { formula: formula.slice(0, 50) });
        }
      }
      
      // check-sat command
      else if (trimmed === '(check-sat)') {
        logger.debug('Checking satisfiability...');
        const satResult = await solver.check();
        
        if (satResult === 'unsat') {
          // UNSAT = No counter-example found = Code is CORRECT! ✅
          return {
            success: true,
            result: 'unsat',
            output: 'unsat',
            constraintsChecked,
          };
        } else if (satResult === 'sat') {
          // SAT = Counter-example found = Code has BUG! ❌
          const model = solver.model();
          const z3Model = extractZ3Model(model, declarations);
          
          return {
            success: false,
            result: 'sat',
            model: z3Model,
            counterExample: generateCounterExample(z3Model, constraintsChecked),
            output: 'sat',
            constraintsChecked,
          };
        } else {
          // UNKNOWN = Z3 couldn't decide
          return {
            success: false,
            result: 'unknown',
            output: 'unknown',
            constraintsChecked,
          };
        }
      }
    } catch (parseError) {
      logger.warn('Failed to parse SMT-LIB command', { line: trimmed, error: parseError });
    }
  }

  // If we reach here, no check-sat was found
  logger.warn('No check-sat command found in SMT-LIB');
  return {
    success: false,
    result: 'unknown',
    output: 'No check-sat command found',
    constraintsChecked,
  };
}

/**
 * Translate SMT-LIB formula to Z3 expression
 * 
 * This is a simplified parser for common patterns.
 * For production, consider using a proper SMT-LIB parser.
 */
function translateFormulaToZ3(
  formula: string,
  declarations: Map<string, any>,
  ctx: any
): any {
  try {
    formula = formula.trim();

    // Handle boolean variables directly
    if (declarations.has(formula) && !formula.includes('(')) {
      return declarations.get(formula);
    }

    // Handle negation: (not expr)
    if (formula.startsWith('(not ')) {
      const inner = formula.slice(5, -1).trim();
      const innerExpr = translateFormulaToZ3(inner, declarations, ctx);
      if (innerExpr) {
        return ctx.Not(innerExpr);
      }
    }

    // Handle and: (and expr1 expr2 ...)
    if (formula.startsWith('(and ')) {
      const subFormulas = extractSubFormulas(formula.slice(5, -1));
      const exprs = subFormulas
        .map(f => translateFormulaToZ3(f, declarations, ctx))
        .filter(e => e !== null);
      
      if (exprs.length > 0) {
        return ctx.And(...exprs);
      }
    }

    // Handle or: (or expr1 expr2 ...)
    if (formula.startsWith('(or ')) {
      const subFormulas = extractSubFormulas(formula.slice(4, -1));
      const exprs = subFormulas
        .map(f => translateFormulaToZ3(f, declarations, ctx))
        .filter(e => e !== null);
      
      if (exprs.length > 0) {
        return ctx.Or(...exprs);
      }
    }

    // Handle implication: (=> expr1 expr2)
    if (formula.startsWith('(=> ')) {
      const subFormulas = extractSubFormulas(formula.slice(4, -1));
      if (subFormulas.length === 2) {
        const antecedent = translateFormulaToZ3(subFormulas[0], declarations, ctx);
        const consequent = translateFormulaToZ3(subFormulas[1], declarations, ctx);
        if (antecedent && consequent) {
          return ctx.Implies(antecedent, consequent);
        }
      }
    }

    // Handle arithmetic expressions first (needed for comparisons)
    
    // Handle addition: (+ a b c ...)
    if (formula.startsWith('(+ ')) {
      const operands = extractSubFormulas(formula.slice(3, -1));
      const values = operands.map(op => {
        const trimmed = op.trim();
        if (/^-?\d+$/.test(trimmed)) {
          return parseInt(trimmed);
        }
        return declarations.get(trimmed);
      }).filter(v => v !== undefined);
      
      if (values.length > 0) {
        return values.reduce((acc, val) => 
          typeof acc === 'number' && typeof val === 'number' 
            ? acc + val 
            : typeof acc === 'number' 
              ? val.add(acc)
              : acc.add(val)
        );
      }
    }

    // Handle subtraction: (- a b)
    if (formula.startsWith('(- ')) {
      const operands = extractSubFormulas(formula.slice(3, -1));
      if (operands.length === 2) {
        const a = parseOperand(operands[0], declarations);
        const b = parseOperand(operands[1], declarations);
        if (a !== null && b !== null) {
          return typeof a === 'number' && typeof b === 'number'
            ? a - b
            : typeof a === 'number'
              ? b.sub(a).mul(-1)
              : a.sub(b);
        }
      }
    }

    // Handle comparisons with expressions
    
    // Handle >=, <=, >, <
    const compMatch = formula.match(/^\((>=|<=|>|<)\s+(.+)\)$/);
    if (compMatch) {
      const [, op, rest] = compMatch;
      const operands = extractSubFormulas(rest);
      if (operands.length === 2) {
        const left = parseOperand(operands[0], declarations);
        const right = parseOperand(operands[1], declarations);
        
        if (left !== null && right !== null) {
          const leftExpr = typeof left === 'number' ? left : left;
          const rightExpr = typeof right === 'number' ? right : right;
          
          if (typeof leftExpr !== 'number') {
            switch (op) {
              case '>=': return leftExpr.ge(rightExpr);
              case '<=': return leftExpr.le(rightExpr);
              case '>': return leftExpr.gt(rightExpr);
              case '<': return leftExpr.lt(rightExpr);
            }
          }
        }
      }
    }

    // Handle equality: (= expr1 expr2)
    if (formula.startsWith('(= ')) {
      const operands = extractSubFormulas(formula.slice(3, -1));
      if (operands.length === 2) {
        const left = parseOperand(operands[0], declarations);
        const right = parseOperand(operands[1], declarations);
        
        if (left !== null && right !== null) {
          if (typeof left === 'number' && typeof right === 'number') {
            return left === right ? ctx.Bool.val(true) : ctx.Bool.val(false);
          } else if (typeof left === 'number') {
            return right.eq(left);
          } else {
            return left.eq(right);
          }
        }
      }
    }

    // Handle distinct: (distinct var1 var2)
    if (formula.startsWith('(distinct ')) {
      const operands = extractSubFormulas(formula.slice(10, -1));
      if (operands.length === 2) {
        const left = parseOperand(operands[0], declarations);
        const right = parseOperand(operands[1], declarations);
        
        if (left !== null && right !== null) {
          if (typeof left !== 'number') {
            return left.neq(right);
          }
        }
      }
    }

    logger.warn('Could not translate formula', { formula: formula.slice(0, 50) });
    return null;

  } catch (error) {
    logger.error('Error translating formula', { formula, error });
    return null;
  }
}

/**
 * Parse an operand (can be a number, variable, or expression)
 */
function parseOperand(operand: string, declarations: Map<string, any>): any {
  operand = operand.trim();
  
  // Check if it's a number
  if (/^-?\d+$/.test(operand)) {
    return parseInt(operand);
  }
  
  // Check if it's a variable
  if (declarations.has(operand)) {
    return declarations.get(operand);
  }
  
  // It might be an expression, recursively parse
  if (operand.startsWith('(')) {
    return translateFormulaToZ3(operand, declarations, declarations.get('__ctx__'));
  }
  
  return null;
}

/**
 * Extract sub-formulas from compound expression
 * Simple implementation - for production, use proper S-expression parser
 */
function extractSubFormulas(content: string): string[] {
  const formulas: string[] = [];
  let depth = 0;
  let current = '';

  for (const char of content) {
    if (char === '(') {
      depth++;
      current += char;
    } else if (char === ')') {
      depth--;
      current += char;
      if (depth === 0 && current.trim()) {
        formulas.push(current.trim());
        current = '';
      }
    } else if (char === ' ' && depth === 0) {
      if (current.trim()) {
        formulas.push(current.trim());
        current = '';
      }
    } else {
      current += char;
    }
  }

  if (current.trim()) {
    formulas.push(current.trim());
  }

  return formulas;
}

/**
 * Extract Z3 model from solver result
 */
function extractZ3Model(model: any, declarations: Map<string, any>): Z3Model {
  const variables: Record<string, Z3Value> = {};

  for (const [varName, variable] of declarations.entries()) {
    // Skip internal keys
    if (varName.startsWith('__')) {
      continue;
    }
    
    try {
      const value = model.eval(variable);
      
      // Try to get sort, handle different API versions
      let sortStr = 'Unknown';
      try {
        if (typeof variable.sort === 'function') {
          sortStr = variable.sort().toString();
        } else if (variable.sort) {
          sortStr = variable.sort.toString();
        } else if (variable.ctx && variable.ctx.getSort) {
          sortStr = variable.ctx.getSort(variable).toString();
        }
      } catch {
        // If sort extraction fails, infer from value
        if (value.toString() === 'true' || value.toString() === 'false') {
          sortStr = 'Bool';
        } else if (!isNaN(parseInt(value.toString()))) {
          sortStr = 'Int';
        }
      }
      
      variables[varName] = {
        sort: sortStr,
        value: value.toString(),
        interpretation: value.asString?.() || value.toString(),
      };
    } catch (error) {
      logger.warn('Could not extract value', { varName, error });
    }
  }

  return { variables };
}

/**
 * Generate counter-example with suggested fix
 */
function generateCounterExample(
  model: Z3Model,
  constraints: string[]
): Z3CounterExample {
  // Find which constraint might be violated
  const violatedConstraint = constraints[constraints.length - 1] || 'Unknown';

  // Format the model as a trace
  const trace = Object.entries(model.variables)
    .map(([name, value]) => `${name} = ${value.value}`)
    .join('\n');

  // Generate suggested fix based on the model
  const suggestedFix = `
The Z3 solver found a counter-example that violates the constraints.

Values that trigger the bug:
${trace}

Violated constraint:
${violatedConstraint}

Suggested fixes:
1. Add stronger precondition checks to prevent these values
2. Ensure idempotency by tracking processed requests
3. Verify balance checks happen before state updates
4. Use atomic transactions to prevent partial updates
`;

  return {
    violatedConstraint,
    model,
    trace,
    suggestedFix: suggestedFix.trim(),
  };
}

