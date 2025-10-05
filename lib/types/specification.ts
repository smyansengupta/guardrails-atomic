import { z } from 'zod';

// Zod schema for runtime validation
export const SpecificationSchema = z.object({
  name: z.string(),
  signature: z.object({
    params: z.array(z.object({
      name: z.string(),
      type: z.string(),
    })),
    returnType: z.string(),
  }),
  preconditions: z.array(z.string()),
  postconditions: z.array(z.string()),
  invariants: z.array(z.object({
    type: z.enum(['idempotent', 'no_double_spend', 'atomic_no_partial_commit', 'conservation']),
    params: z.record(z.string(), z.any()).optional(),
    description: z.string().optional(),
  })),
  faultModel: z.object({
    delivery: z.enum(['at_least_once', 'exactly_once', 'at_most_once']),
    reorder: z.boolean(),
    crash_restart: z.boolean(),
    network_partition: z.boolean().optional(),
  }),
  bounds: z.object({
    accts: z.number().optional(),
    retries: z.number().optional(),
    messages: z.number().optional(),
    depth: z.number().optional(),
  }),
});

// TypeScript type inferred from schema
export type Specification = z.infer<typeof SpecificationSchema>;

export interface Parameter {
  name: string;
  type: string;
}

export interface FunctionSignature {
  params: Parameter[];
  returnType: string;
}

export interface Invariant {
  type: 'idempotent' | 'no_double_spend' | 'atomic_no_partial_commit' | 'conservation';
  params?: Record<string, any>;
  description?: string;
}

export interface FaultModel {
  delivery: 'at_least_once' | 'exactly_once' | 'at_most_once';
  reorder: boolean;
  crash_restart: boolean;
  network_partition?: boolean;
}

export interface Bounds {
  accts?: number;
  retries?: number;
  messages?: number;
  depth?: number;
}
