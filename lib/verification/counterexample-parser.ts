import { CounterExample, InvariantViolation, ExecutionStep } from '@/lib/types/verification';

/**
 * Parse TLC output to extract counterexamples
 *
 * @param tlcOutput - Raw TLC output string
 * @returns Parsed counterexample with execution trace
 *
 * TLC outputs counterexamples in this format:
 * ```
 * Error: Invariant TypeOK is violated.
 * The behavior up to this point is:
 * State 1: <Initial predicate>
 * /\ var1 = value1
 * /\ var2 = value2
 *
 * State 2: <Action line ...>
 * /\ var1 = value1'
 * /\ var2 = value2'
 * ```
 */
export function parseCounterExample(tlcOutput: string): CounterExample | null {
  // Check if there's an error/violation
  const errorMatch = tlcOutput.match(/Error:\s+Invariant\s+(\w+)\s+is\s+violated/i);
  if (!errorMatch) {
    return null;
  }

  const invariantName = errorMatch[1];

  // Extract the behavior/trace section
  const behaviorMatch = tlcOutput.match(/The behavior up to this point is:([\s\S]*?)(?:Error:|$)/i);
  if (!behaviorMatch) {
    // Return basic counterexample without trace
    return {
      schedule: [],
      violation: {
        invariantName,
        message: `Invariant ${invariantName} was violated`,
      },
      suggestedFix: `Review the ${invariantName} invariant and ensure the code satisfies it`,
    };
  }

  const behaviorText = behaviorMatch[1];

  // Parse individual states
  const states: ExecutionStep[] = [];
  const stateBlocks = behaviorText.split(/State\s+\d+:/);

  for (let i = 1; i < stateBlocks.length; i++) {
    const stateBlock = stateBlocks[i];

    // Extract action name from lines like "<Action line 42, col 5 to line 45, col 20 of module Spec>"
    const actionMatch = stateBlock.match(/<(\w+)\s+line/i) || stateBlock.match(/<(.+?)>/);
    const action = actionMatch ? actionMatch[1].trim() : (i === 1 ? 'Init' : 'Unknown');

    // Extract variable assignments (lines like "/\ var = value")
    const state: Record<string, any> = {};
    const assignmentMatches = stateBlock.matchAll(/\/\\\s*(\w+)\s*=\s*(.+?)(?=\n|$)/g);

    for (const match of assignmentMatches) {
      const varName = match[1];
      let value = match[2].trim();

      // Try to parse value as JSON for structured data
      try {
        // Remove TLA+ specific syntax
        value = value.replace(/<<|>>/g, '').replace(/\[|\]/g, '');
        state[varName] = value;
      } catch {
        state[varName] = value;
      }
    }

    states.push({
      action,
      state,
    });
  }

  return {
    schedule: states,
    violation: {
      invariantName,
      message: `Invariant ${invariantName} was violated after ${states.length} steps`,
    },
    suggestedFix: generateSuggestedFix(invariantName, states),
  };
}

/**
 * Generate a suggested fix based on the invariant type and trace
 */
function generateSuggestedFix(invariantName: string, states: ExecutionStep[]): string {
  const invLower = invariantName.toLowerCase();

  if (invLower.includes('idempotent')) {
    return 'Check if the request ID is already in the processed set before executing the operation. Add: if (processed.has(requestId)) return;';
  }

  if (invLower.includes('conservation')) {
    return 'Ensure that all operations preserve the total sum. Check for missing increments or decrements.';
  }

  if (invLower.includes('atomic') || invLower.includes('partial')) {
    return 'Use transactions or implement rollback logic to ensure all-or-nothing semantics.';
  }

  if (invLower.includes('doublespend') || invLower.includes('double_spend')) {
    return 'Add balance checks before deductions and ensure atomic updates.';
  }

  if (invLower.includes('typeok') || invLower.includes('type')) {
    return 'Check variable types and ensure all operations maintain type correctness.';
  }

  return `Review the ${invariantName} invariant definition and ensure the implementation satisfies all conditions.`;
}

/**
 * Parse invariant violations from TLC output
 *
 * @param tlcOutput - Raw TLC output string
 * @returns List of invariant violations
 *
 * Looks for patterns like:
 * - "Error: Invariant X is violated"
 * - "Invariant X is violated"
 */
export function parseViolations(tlcOutput: string): InvariantViolation[] {
  const violations: InvariantViolation[] = [];

  // Pattern 1: "Error: Invariant X is violated"
  const errorMatches = tlcOutput.matchAll(/(?:Error:\s+)?Invariant\s+(\w+)\s+is\s+violated\.?/gi);

  for (const match of errorMatches) {
    const invariantName = match[1];

    // Try to extract more context around the violation
    const contextMatch = tlcOutput.match(
      new RegExp(`Invariant\\s+${invariantName}[\\s\\S]{0,200}`, 'i')
    );

    violations.push({
      invariantName,
      message: contextMatch
        ? contextMatch[0].trim()
        : `Invariant ${invariantName} is violated`,
    });
  }

  // Pattern 2: General errors
  if (violations.length === 0 && /error/i.test(tlcOutput)) {
    const errorLines = tlcOutput.split('\n').filter(line => /error/i.test(line));
    if (errorLines.length > 0) {
      violations.push({
        invariantName: 'Unknown',
        message: errorLines[0].trim(),
      });
    }
  }

  return violations;
}

/**
 * Generate repair feedback from counterexample
 *
 * @param counterExample - The parsed counterexample
 * @returns Human-readable repair feedback for the LLM
 */
export function generateRepairFeedback(counterExample: CounterExample): string {
  const { violation, schedule, suggestedFix } = counterExample;

  const feedbackParts: string[] = [];

  // Header with violation
  feedbackParts.push(`VIOLATION: ${violation.invariantName} invariant failed`);
  feedbackParts.push('');

  // Execution trace
  if (schedule.length > 0) {
    feedbackParts.push('EXECUTION TRACE:');
    schedule.forEach((step, index) => {
      const stateDesc = Object.entries(step.state)
        .map(([key, value]) => `${key}=${JSON.stringify(value)}`)
        .join(', ');
      feedbackParts.push(`${index + 1}. ${step.action}${stateDesc ? ` - State: ${stateDesc}` : ''}`);
    });
    feedbackParts.push('');
  }

  // Issue description
  feedbackParts.push(`ISSUE: ${violation.message}`);
  feedbackParts.push('');

  // Suggested fix
  feedbackParts.push(`FIX: ${suggestedFix}`);

  return feedbackParts.join('\n');
}
