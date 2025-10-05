export interface VerificationResult {
  success: boolean;
  iterations: number;
  finalCode?: string;
  tlaSpec?: string;
  proofReport?: ProofReport;
  iterationHistory?: IterationRecord[];
  error?: string;
}

export interface IterationRecord {
  iteration: number;
  code: string;
  tlaSpec: string;
  tlcResult: TLCResult;
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
  statesExplored: number;
  invariantsVerified: string[];
  faultScenariosChecked: string[];
  guarantees: string[];
  timestamp: string;
  duration: number;
}
