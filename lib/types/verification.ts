export interface VerificationResult {
  success: boolean;
  iterations: number;
  finalCode?: string;
  tlaSpec?: string; // Legacy, will be deprecated
  z3Constraints?: string; // New: Z3 SMT-LIB format
  proofReport?: ProofReport;
  iterationHistory?: IterationRecord[];
  error?: string;
}

export interface IterationRecord {
  iteration: number;
  code: string;
  tlaSpec?: string; // Legacy
  z3Constraints?: string; // New
  tlcResult?: TLCResult; // Legacy
  z3Result?: Z3Result; // New
  feedback?: string;
}

export interface TLCResult {
  success: boolean;
  statesExplored: number;
  invariantsChecked: string[];
  violations?: InvariantViolation[];
  counterExample?: CounterExample;
  output: string;
  duration?: number;
}

export interface InvariantViolation {
  invariantName: string;
  message: string;
  trace?: ExecutionStep[];
}

export interface CounterExample {
  schedule: ExecutionStep[];
  violation: InvariantViolation;
  suggestedFix: string;
}

export interface ExecutionStep {
  action: string;
  state: Record<string, any>;
  params?: Record<string, any>;
  timestamp?: number;
}

export interface ProofReport {
  statesExplored?: number; // Optional for Z3 (not applicable)
  constraintsChecked?: number; // New: for Z3
  invariantsVerified: string[];
  faultScenariosChecked: string[];
  guarantees: string[];
  timestamp: string;
  duration: number;
}

/**
 * Z3 Result types (imported from z3-ast.ts but re-exported for convenience)
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
