/**
 * Type definitions for Z3 constraint generation
 * 
 * Z3 is an SMT (Satisfiability Modulo Theories) solver that checks
 * satisfiability of logical formulas over different theories.
 */

export interface Z3Module {
  name: string;
  sorts: Z3Sort[];
  constants: Z3Constant[];
  functions: Z3Function[];
  constraints: Z3Constraint[];
  assertions: Z3Assertion[];
  checkSat: boolean;
  source?: string;
}

export interface Z3Sort {
  name: string;
  type: 'Int' | 'Bool' | 'Array' | 'Datatype' | 'String';
  elementType?: string; // For arrays: Array(Int, Int) means index:Int -> value:Int
  constructors?: Z3Constructor[]; // For datatypes
}

export interface Z3Constructor {
  name: string;
  fields: Array<{
    name: string;
    type: string;
  }>;
}

export interface Z3Constant {
  name: string;
  sort: string; // e.g., "Int", "Bool", "Array(String, Int)"
  value?: string | number | boolean;
}

export interface Z3Function {
  name: string;
  parameters: Array<{
    name: string;
    sort: string;
  }>;
  returnSort: string;
  body?: string; // Optional: define the function
}

export interface Z3Constraint {
  name: string;
  formula: string;
  description?: string;
  type: 'precondition' | 'postcondition' | 'invariant' | 'transition';
}

export interface Z3Assertion {
  formula: string;
  comment?: string;
}

/**
 * Z3 verification result
 */
export interface Z3Result {
  success: boolean;
  result: 'sat' | 'unsat' | 'unknown';
  model?: Z3Model;
  counterExample?: Z3CounterExample;
  output: string;
  duration?: number;
  constraintsChecked: string[];
}

export interface Z3Model {
  variables: Record<string, Z3Value>;
  arrays?: Record<string, Record<string, Z3Value>>;
}

export interface Z3Value {
  sort: string;
  value: string | number | boolean;
  interpretation?: string;
}

export interface Z3CounterExample {
  violatedConstraint: string;
  model: Z3Model;
  trace: string;
  suggestedFix: string;
}

