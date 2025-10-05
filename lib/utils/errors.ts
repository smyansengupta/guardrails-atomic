export class SpecificationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'SpecificationError';
  }
}

export class VerificationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'VerificationError';
  }
}

export class TLCExecutionError extends Error {
  constructor(message: string, public readonly output?: string) {
    super(message);
    this.name = 'TLCExecutionError';
  }
}

export class CodeGenerationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'CodeGenerationError';
  }
}

export class TLAGenerationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'TLAGenerationError';
  }
}

export class NLToYAMLError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'NLToYAMLError';
  }
}
