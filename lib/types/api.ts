import { Specification } from './specification';
import { VerificationResult } from './verification';

// POST /api/verify
export interface VerifyRequest {
  spec: string; // YAML string
  maxIterations?: number;
}

export interface VerifyResponse {
  success: boolean;
  result?: VerificationResult;
  error?: string;
}

// POST /api/verify-stream (SSE endpoint)
export interface VerifyStreamRequest {
  spec: string; // YAML string
  maxIterations?: number;
}

// Server-Sent Event types for streaming verification progress
export type VerificationEvent =
  | ProgressEvent
  | IterationStartEvent
  | IterationCompleteEvent
  | CodeGeneratedEvent
  | TLAGeneratedEvent
  | TLCStartEvent
  | TLCCompleteEvent
  | VerificationCompleteEvent
  | ErrorEvent;

export interface ProgressEvent {
  type: 'progress';
  phase: 'parsing' | 'generating_code' | 'generating_tla' | 'running_tlc' | 'analyzing_results';
  message: string;
  timestamp: string;
}

export interface IterationStartEvent {
  type: 'iteration_start';
  iteration: number;
  maxIterations: number;
  isRepair: boolean;
  timestamp: string;
}

export interface IterationCompleteEvent {
  type: 'iteration_complete';
  iteration: number;
  success: boolean;
  statesExplored?: number;
  violationFound?: boolean;
  timestamp: string;
}

export interface CodeGeneratedEvent {
  type: 'code_generated';
  iteration: number;
  codeLength: number;
  preview: string; // First 100 chars
  timestamp: string;
}

export interface TLAGeneratedEvent {
  type: 'tla_generated';
  iteration: number;
  tlaLength: number;
  timestamp: string;
}

export interface TLCStartEvent {
  type: 'tlc_start';
  iteration: number;
  timestamp: string;
}

export interface TLCCompleteEvent {
  type: 'tlc_complete';
  iteration: number;
  success: boolean;
  statesExplored: number;
  duration: number; // milliseconds
  timestamp: string;
}

export interface VerificationCompleteEvent {
  type: 'verification_complete';
  success: boolean;
  iterations: number;
  result?: VerificationResult;
  timestamp: string;
}

export interface ErrorEvent {
  type: 'error';
  phase: string;
  message: string;
  timestamp: string;
}

// POST /api/validate
export interface ValidateRequest {
  spec: string; // YAML string
}

export interface ValidateResponse {
  valid: boolean;
  errors?: string[];
  parsed?: Specification;
}

// POST /api/generate-spec
export interface GenerateSpecRequest {
  naturalLanguage: string; // Natural language description (min 10 chars)
  context?: string; // Optional additional context
}

export interface GenerateSpecResponse {
  yaml?: string; // Generated YAML spec
  error?: string;
  warnings?: string[]; // Suggestions or things user should review
  // Rate limit info (only present when rate limited)
  remainingSeconds?: number; // Seconds until rate limit resets
  resetAt?: string; // ISO timestamp when rate limit resets
}

// GET /api/examples
export interface ExampleSpec {
  name: string;
  description: string;
  yaml: string;
  category: 'transfer' | 'write' | 'saga';
}

export interface ExamplesResponse {
  examples: ExampleSpec[];
}
