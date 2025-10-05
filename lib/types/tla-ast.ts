export interface TLAModule {
  name: string;
  extends: string[];
  constants: TLAConstant[];
  variables: TLAVariable[];
  init: string;
  actions: TLAAction[];
  invariants: TLAInvariant[];
  next: string;
  spec: string;
  source?: string;
}

export interface TLAConstant {
  name: string;
  type?: string;
  value?: string;
}

export interface TLAVariable {
  name: string;
  type?: string;
  description?: string;
}

export interface TLAAction {
  name: string;
  parameters: string[];
  guards: string[];
  updates: string[];
  unchanged: string[];
}

export interface TLAInvariant {
  name: string;
  predicate: string;
  description?: string;
}
