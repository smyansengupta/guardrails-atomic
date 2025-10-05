import { readFile } from 'fs/promises';
import path from 'path';
import { Specification, FunctionSignature, Invariant } from '@/lib/types/specification';
import { generateWithOpenRouter } from '@/lib/services/openrouter.service';
import { CodeGenerationError } from '@/lib/utils/errors';

/**
 * Generate TypeScript code from specification using LLM
 *
 * @param spec - The specification to generate code from
 * @param feedback - Optional feedback from previous iteration for repair
 * @returns Generated TypeScript code as a string
 */
export async function generateCode(
  spec: Specification,
  feedback?: string
): Promise<string> {
  try {
    // Step 1: Load appropriate template
    const templateName = feedback ? 'code-repair.txt' : 'code-generation.txt';
    const templatePath = path.join(process.cwd(), 'templates', 'prompts', templateName);
    let template = await readFile(templatePath, 'utf-8');

    // Step 2: Populate template with spec details
    if (feedback) {
      // Repair mode: populate with previous code and feedback
      const feedbackComponents = parseFeedback(feedback);
      template = populateRepairTemplate(template, feedbackComponents);
    } else {
      // Initial generation mode: populate with spec details
      template = populateInitialTemplate(template, spec);
    }

    // Step 3: Call OpenRouter API
    const response = await generateWithOpenRouter(template);

    // Step 4: Extract code from markdown wrapper
    const code = extractCodeFromMarkdown(response);

    // Step 5: Validate and return
    if (!code || code.trim().length === 0) {
      throw new CodeGenerationError('LLM returned empty code');
    }

    return code;
  } catch (error) {
    if (error instanceof CodeGenerationError) {
      throw error;
    }
    throw new CodeGenerationError(
      `Failed to generate code: ${error instanceof Error ? error.message : String(error)}`
    );
  }
}

/**
 * Populate initial code generation template with spec details
 */
function populateInitialTemplate(template: string, spec: Specification): string {
  return template
    .replace('{{name}}', spec.name)
    .replace('{{signature}}', formatSignature(spec.signature, spec.name))
    .replace('{{preconditions}}', formatPreconditions(spec.preconditions))
    .replace('{{postconditions}}', formatPostconditions(spec.postconditions))
    .replace('{{invariants}}', formatInvariants(spec.invariants))
    .replace('{{delivery}}', spec.faultModel.delivery)
    .replace('{{reorder}}', String(spec.faultModel.reorder))
    .replace('{{crash_restart}}', String(spec.faultModel.crash_restart));
}

/**
 * Populate repair template with previous code and feedback
 */
function populateRepairTemplate(
  template: string,
  feedback: FeedbackComponents
): string {
  return template
    .replace('{{code}}', feedback.code)
    .replace('{{violation}}', feedback.violation)
    .replace('{{trace}}', feedback.trace)
    .replace('{{suggestion}}', feedback.suggestion);
}

/**
 * Format function signature for prompt
 */
export function formatSignature(signature: FunctionSignature, name: string): string {
  const params = signature.params
    .map(p => `${p.name}: ${p.type}`)
    .join(', ');
  return `function ${name}(${params}): ${signature.returnType}`;
}

/**
 * Format preconditions as bulleted list
 */
export function formatPreconditions(preconditions: string[]): string {
  if (preconditions.length === 0) {
    return '(none)';
  }
  return preconditions.map(p => `- ${p}`).join('\n');
}

/**
 * Format postconditions as bulleted list
 */
export function formatPostconditions(postconditions: string[]): string {
  if (postconditions.length === 0) {
    return '(none)';
  }
  return postconditions.map(p => `- ${p}`).join('\n');
}

/**
 * Format invariants with descriptions
 */
export function formatInvariants(invariants: Invariant[]): string {
  if (invariants.length === 0) {
    return '(none)';
  }

  return invariants.map(inv => {
    const description = getInvariantDescription(inv.type);
    const params = inv.params ? ` (${JSON.stringify(inv.params)})` : '';
    return `- ${inv.type}${params}: ${description}`;
  }).join('\n');
}

/**
 * Get human-readable description for invariant type
 */
function getInvariantDescription(type: string): string {
  switch (type) {
    case 'idempotent':
      return 'Repeated execution with same request ID has no additional effect';
    case 'no_double_spend':
      return 'Resources cannot be spent twice';
    case 'atomic_no_partial_commit':
      return 'Either all state changes happen or none (all-or-nothing)';
    case 'conservation':
      return 'Total sum of resources remains constant across operations';
    default:
      return 'Property must be maintained';
  }
}

/**
 * Extract TypeScript code from markdown wrapper
 */
export function extractCodeFromMarkdown(response: string): string {
  // Try to find code block with typescript, ts, or no language specified
  const patterns = [
    /```typescript\n([\s\S]*?)\n```/,
    /```ts\n([\s\S]*?)\n```/,
    /```\n([\s\S]*?)\n```/,
  ];

  for (const pattern of patterns) {
    const match = response.match(pattern);
    if (match) {
      return match[1].trim();
    }
  }

  // Fallback: return trimmed response if no markdown wrapper found
  return response.trim();
}

/**
 * Feedback components extracted from repair feedback string
 */
interface FeedbackComponents {
  code: string;
  violation: string;
  trace: string;
  suggestion: string;
}

/**
 * Parse feedback string into components for repair template
 *
 * The feedback string from generateRepairFeedback() has this format:
 * ```
 * VIOLATION: <violation>
 *
 * EXECUTION TRACE:
 * <trace>
 *
 * ISSUE: <issue>
 *
 * FIX: <suggestion>
 * ```
 *
 * However, we need the original code too. The CEGIS loop should pass
 * a feedback string that includes the code. For now, we'll extract
 * what we can from the feedback and handle missing code gracefully.
 */
export function parseFeedback(feedback: string): FeedbackComponents {
  // Extract violation
  const violationMatch = feedback.match(/VIOLATION:\s*(.+?)(?=\n\n|\n[A-Z]+:|$)/s);
  const violation = violationMatch ? violationMatch[1].trim() : 'Unknown violation';

  // Extract execution trace
  const traceMatch = feedback.match(/EXECUTION TRACE:\s*([\s\S]+?)(?=\n\n[A-Z]+:|$)/);
  const trace = traceMatch ? traceMatch[1].trim() : 'No trace available';

  // Extract issue
  const issueMatch = feedback.match(/ISSUE:\s*(.+?)(?=\n\n|\n[A-Z]+:|$)/s);
  const issue = issueMatch ? issueMatch[1].trim() : '';

  // Extract suggested fix
  const fixMatch = feedback.match(/FIX:\s*(.+?)$/s);
  const suggestion = fixMatch ? fixMatch[1].trim() : 'Review and fix the violation';

  // Try to extract code if it's in the feedback
  // The CEGIS loop should include this, but if not, we'll use a placeholder
  const codeMatch = feedback.match(/ORIGINAL CODE:\s*([\s\S]+?)(?=\n\n[A-Z]+:|$)/);
  const code = codeMatch ? codeMatch[1].trim() : '// Previous code not available';

  return {
    code,
    violation: `${violation}${issue ? `\n${issue}` : ''}`,
    trace,
    suggestion,
  };
}
