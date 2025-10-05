import path from 'path';
import { readFile } from 'fs/promises';
import { z } from 'zod';

import { Specification } from '@/lib/types/specification';
import { TLAModule, TLAAction, TLAInvariant, TLAVariable } from '@/lib/types/tla-ast';
import { generateWithOpenRouter } from '@/lib/services/openrouter.service';
import { logger } from '@/lib/utils/logger';
import { TLAGenerationError } from '@/lib/utils/errors';

const RESPONSE_SCHEMA = z.object({
  module: z.object({
    name: z.string(),
    extends: z.array(z.string()).default([]),
    constants: z
      .array(
        z.object({
          name: z.string(),
          type: z.string().optional(),
          value: z.string().optional(),
        })
      )
      .default([]),
    variables: z
      .array(
        z.object({
          name: z.string(),
          type: z.string().optional(),
          description: z.string().optional(),
        })
      )
      .default([]),
    init: z.string(),
    actions: z
      .array(
        z.object({
          name: z.string(),
          parameters: z.array(z.string()).default([]),
          guards: z.array(z.string()).default([]),
          updates: z.array(z.string()).default([]),
          unchanged: z.array(z.string()).default([]),
        })
      )
      .default([]),
    invariants: z
      .array(
        z.object({
          name: z.string(),
          predicate: z.string(),
          description: z.string().optional(),
        })
      )
      .default([]),
    next: z.string(),
    spec: z.string(),
    source: z.string().optional(),
  }),
  config: z.string(),
});

type TLAGenerationResponse = z.infer<typeof RESPONSE_SCHEMA>;

type CachedResponse = {
  module: TLAModule;
  config: string;
};

const PROMPT_PATH = path.join(process.cwd(), 'templates', 'prompts', 'tla-generation.txt');
const generationCache = new Map<string, CachedResponse>();
let promptTemplate: string | null = null;

export async function generateTLAModule(spec: Specification): Promise<TLAModule> {
  const { module } = await synthesizeTLAArtifacts(spec);
  return module;
}

export async function generateTLCConfig(spec: Specification): Promise<string> {
  const { config } = await synthesizeTLAArtifacts(spec);
  return config;
}

export function tlaModuleToString(module: TLAModule): string {
  if (module.source) {
    return normalizeMultiline(module.source);
  }

  const lines: string[] = [];
  lines.push(`---------------------------- MODULE ${module.name} ----------------------------`);

  if (module.extends?.length) {
    lines.push(`EXTENDS ${module.extends.join(', ')}`);
    lines.push('');
  }

  if (module.constants?.length) {
    const constantsLine = module.constants.map(constant => constant.name).join(', ');
    lines.push(`CONSTANTS ${constantsLine}`);
    lines.push('');
  }

  if (module.variables?.length) {
    lines.push('VARIABLES');
    module.variables.forEach(variable => {
      lines.push(`    ${variable.name}`);
    });
    lines.push('');
  }

  const varTuple = module.variables?.length ? module.variables.map(variable => variable.name).join(', ') : '';
  if (varTuple) {
    lines.push(`vars == <<${varTuple}>>`);
    lines.push('');
  }

  const typeOkInvariant = module.invariants?.find(inv => inv.name === 'TypeOK');
  if (typeOkInvariant) {
    lines.push('\\* Type invariant');
    lines.push(`${typeOkInvariant.name} ==`);
    lines.push(formatIndented(typeOkInvariant.predicate));
    lines.push('');
  }

  lines.push('\\* Initial state');
  lines.push('Init ==');
  lines.push(formatIndented(module.init));
  lines.push('');

  if (module.actions?.length) {
    module.actions.forEach(action => {
      const parameters = action.parameters?.length ? `(${action.parameters.join(', ')})` : '';
      lines.push(`\\* ${action.name} action`);
      lines.push(`${action.name}${parameters} ==`);

      action.guards?.forEach((guard, index) => {
        const prefix = index === 0 ? '    /\\' : '    /\\';
        lines.push(`${prefix} ${guard}`);
      });

      action.updates?.forEach(update => {
        lines.push(`    /\\ ${update}`);
      });

      if (action.unchanged?.length) {
        lines.push(`    /\\ UNCHANGED <<${action.unchanged.join(', ')}>>`);
      }

      lines.push('');
    });
  }

  const remainingInvariants = (module.invariants ?? []).filter(inv => inv.name !== 'TypeOK');
  remainingInvariants.forEach(inv => {
    lines.push(`\\* ${inv.description ?? inv.name}`);
    lines.push(`${inv.name} ==`);
    lines.push(formatIndented(inv.predicate));
    lines.push('');
  });

  lines.push('\\* Next state relation');
  lines.push('Next ==');
  lines.push(formatIndented(module.next));
  lines.push('');

  lines.push('\\* Specification');
  lines.push(`Spec == ${module.spec}`);
  lines.push('');

  const invariantNames = module.invariants?.map(inv => inv.name).join(' /\\ ');
  if (invariantNames) {
    lines.push('\\* Theorem');
    lines.push(`THEOREM Spec => [](${invariantNames})`);
  }

  lines.push('=============================================================================');

  return lines.join('\n');
}

async function synthesizeTLAArtifacts(spec: Specification): Promise<CachedResponse> {
  const cacheKey = JSON.stringify(spec);
  if (generationCache.has(cacheKey)) {
    return generationCache.get(cacheKey)!;
  }

  const template = await loadPromptTemplate();
  const prompt = template.replace('{{SPEC_JSON}}', JSON.stringify(spec, null, 2));

  logger.info('Generating TLA+ module with OpenRouter', { specName: spec.name });

  const rawResponse = await generateWithOpenRouter(prompt);
  const jsonBlock = extractJsonBlock(rawResponse);

  let parsed: TLAGenerationResponse;
  try {
    parsed = RESPONSE_SCHEMA.parse(JSON.parse(jsonBlock));
  } catch (error) {
    throw new TLAGenerationError(`Failed to parse LLM response into TLA module: ${error}`);
  }

  const normalizedModule = normalizeModule(parsed.module, spec.name);
  const normalizedConfig = normalizeMultiline(parsed.config);

  const cached: CachedResponse = {
    module: normalizedModule,
    config: normalizedConfig,
  };

  generationCache.set(cacheKey, cached);

  logger.info('TLA+ synthesis completed', {
    specName: spec.name,
    actions: normalizedModule.actions.length,
    invariants: normalizedModule.invariants.length,
  });

  return cached;
}

async function loadPromptTemplate(): Promise<string> {
  if (promptTemplate) {
    return promptTemplate;
  }

  const content = await readFile(PROMPT_PATH, 'utf-8');
  promptTemplate = content;
  return content;
}

function extractJsonBlock(response: string): string {
  const fenced = response.match(/```json\s*([\s\S]*?)```/i);
  if (fenced && fenced[1]) {
    return fenced[1].trim();
  }

  const firstBrace = response.indexOf('{');
  const lastBrace = response.lastIndexOf('}');
  if (firstBrace === -1 || lastBrace === -1 || lastBrace <= firstBrace) {
    throw new TLAGenerationError('LLM response did not contain a JSON object.');
  }

  return response.slice(firstBrace, lastBrace + 1).trim();
}

function normalizeModule(module: TLAModule, fallbackName: string): TLAModule {
  const constants = (module.constants ?? []).map(constant => ({
      ...constant,
      name: constant.name.trim(),
      type: constant.type?.trim(),
      value: constant.value?.trim(),
    }));

  const variables = (module.variables ?? []).map(variable => ({
      ...variable,
      name: variable.name.trim(),
      type: variable.type?.trim(),
      description: variable.description?.trim(),
    }));

  const normalized: TLAModule = {
    ...module,
    name: module.name || fallbackName,
    extends: module.extends ?? [],
    constants,
    variables,
    init: normalizeMultiline(module.init),
    actions: normalizeActions(module.actions ?? []),
    invariants: ensureTypeOkInvariant(module.invariants ?? [], variables),
    next: normalizeMultiline(module.next),
    spec: normalizeMultiline(module.spec),
    source: module.source ? normalizeMultiline(module.source) : undefined,
  };

  return normalized;
}

function normalizeActions(actions: TLAAction[]): TLAAction[] {
  return actions.map(action => ({
    ...action,
    name: action.name.trim(),
    parameters: (action.parameters ?? []).map(param => param.trim()).filter(Boolean),
    guards: (action.guards ?? []).map(normalizeMultiline).filter(Boolean),
    updates: (action.updates ?? []).map(normalizeMultiline).filter(Boolean),
    unchanged: (action.unchanged ?? []).map(entry => entry.trim()).filter(Boolean),
  }));
}

function ensureTypeOkInvariant(invariants: TLAInvariant[], variables: TLAVariable[]): TLAInvariant[] {
  const hasTypeOk = invariants.some(inv => inv.name === 'TypeOK');
  if (hasTypeOk) {
    return invariants.map(inv => ({
      ...inv,
      predicate: normalizeMultiline(inv.predicate),
      description: inv.description?.trim(),
    }));
  }

  const typePredicates = (variables ?? []).map(variable => {
    if (variable.type) {
      return `/\\ ${variable.name} \\in ${variable.type}`;
    }
    return `/\\ ${variable.name} = ${variable.name}`;
  }) ?? [];

  const predicate = typePredicates.length ? typePredicates.join('\n    ') : 'TRUE';

  return [
    {
      name: 'TypeOK',
      predicate,
      description: 'Automated type invariant',
    },
    ...invariants.map(inv => ({
      ...inv,
      predicate: normalizeMultiline(inv.predicate),
      description: inv.description?.trim(),
    })),
  ];
}

function normalizeMultiline(value?: string): string {
  if (!value) {
    return '';
  }
  return value
    .replace(/\r\n/g, '\n')
    .split('\n')
    .map(line => line.trimEnd())
    .join('\n')
    .trim();
}

function formatIndented(value: string): string {
  return normalizeMultiline(value)
    .split('\n')
    .map(line => `    ${line}`)
    .join('\n');
}
