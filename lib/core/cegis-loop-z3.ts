/**
 * CEGIS Loop with Z3 Verification
 * 
 * Counter-Example Guided Inductive Synthesis using Z3 SMT solver
 * instead of TLA+/TLC.
 */

import { Specification } from '@/lib/types/specification';
import {
  VerificationResult,
  IterationRecord,
  Z3Result,
  ProofReport
} from '@/lib/types/verification';
import { generateCode } from './code-generator';
import { generateZ3Module, z3ModuleToString, generateZ3Config } from '@/lib/verification/z3-generator';
import { runZ3 } from '@/lib/verification/z3-runner';
import { logger } from '@/lib/utils/logger';
import { VerificationError } from '@/lib/utils/errors';

/**
 * Generate a proof report from successful Z3 verification
 */
function generateProofReport(
  z3Result: Z3Result,
  spec: Specification
): ProofReport {
  // Extract fault scenarios checked from the fault model
  const faultScenariosChecked: string[] = [];

  if (spec.faultModel.delivery === 'at_least_once') {
    faultScenariosChecked.push('Duplicate message delivery');
  } else if (spec.faultModel.delivery === 'at_most_once') {
    faultScenariosChecked.push('Message loss');
  }

  if (spec.faultModel.reorder) {
    faultScenariosChecked.push('Message reordering');
  }

  if (spec.faultModel.crash_restart) {
    faultScenariosChecked.push('Process crash and restart');
  }

  if (spec.faultModel.network_partition) {
    faultScenariosChecked.push('Network partition');
  }

  // Generate guarantees from verified invariants
  const guarantees: string[] = spec.invariants.map(inv => {
    switch (inv.type) {
      case 'idempotent':
        return 'Function is idempotent - duplicate requests have no additional effect';
      case 'no_double_spend':
        return 'Resources cannot be spent twice';
      case 'atomic_no_partial_commit':
        return 'All state changes are atomic - no partial commits';
      case 'conservation':
        return 'Total resources are conserved across all operations';
      default:
        return `${inv.type} property is maintained`;
    }
  });

  return {
    constraintsChecked: z3Result.constraintsChecked.length,
    invariantsVerified: spec.invariants.map(inv => inv.type),
    faultScenariosChecked,
    guarantees,
    timestamp: new Date().toISOString(),
    duration: z3Result.duration || 0,
  };
}

/**
 * Generate repair feedback from Z3 counter-example
 */
function generateZ3RepairFeedback(z3Result: Z3Result, currentCode: string): string {
  if (!z3Result.counterExample) {
    return `Z3 found violations but no detailed counter-example is available.\n\nPlease review the code and fix the invariant violations.`;
  }

  const { counterExample } = z3Result;

  return `ORIGINAL CODE:
${currentCode}

Z3 SMT SOLVER FOUND THIS BUG:
${counterExample.violatedConstraint}

COUNTER-EXAMPLE MODEL:
${counterExample.trace}

SUGGESTED FIX:
${counterExample.suggestedFix}`;
}

/**
 * Main CEGIS loop with Z3: iteratively generate code, verify, and repair
 * 
 * @param spec - The specification to verify
 * @param maxIterations - Maximum number of CEGIS iterations (default: 8)
 * @returns The verification result including final code and proof report
 * 
 * The CEGIS loop works as follows:
 * 1. Generate TypeScript code from specification using LLM
 * 2. Translate specification to Z3 SMT constraints
 * 3. Run Z3 solver to check satisfiability
 * 4. If sat (counter-example found), extract model and generate repair feedback
 * 5. Use feedback to regenerate code (repair mode)
 * 6. Repeat until unsat (verified) or max iterations reached
 */
export async function runCEGISLoopZ3(
  spec: Specification,
  maxIterations: number = 8
): Promise<VerificationResult> {
  logger.info(`Starting CEGIS loop (Z3) for spec: ${spec.name}`, { maxIterations });

  const iterationHistory: IterationRecord[] = [];
  let currentCode: string | null = null;
  let feedback: string | undefined = undefined;
  const startTime = Date.now();

  try {
    for (let i = 1; i <= maxIterations; i++) {
      const iterationStart = Date.now();
      logger.info(`CEGIS iteration ${i}/${maxIterations}`);

      // Phase 1: Code Generation
      logger.debug('Phase 1: Generating code', { hasFeedback: !!feedback });
      try {
        currentCode = await generateCode(spec, feedback);
        logger.debug('Code generation successful', {
          codeLength: currentCode.length,
          isRepair: !!feedback
        });
      } catch (error) {
        logger.error(`Code generation failed in iteration ${i}`, error);
        throw new VerificationError(
          `Code generation failed: ${error instanceof Error ? error.message : String(error)}`
        );
      }

      // Phase 2: Z3 Constraint Generation
      logger.debug('Phase 2: Generating Z3 constraints');
      let z3Module;
      let z3Constraints: string;
      let configFile: string;

      try {
        z3Module = generateZ3Module(spec);
        z3Constraints = z3ModuleToString(z3Module);
        configFile = generateZ3Config(spec);
        logger.debug('Z3 constraint generation successful', {
          constraintsLength: z3Constraints.length,
          numConstraints: z3Module.constraints.length,
        });
      } catch (error) {
        logger.error(`Z3 constraint generation failed in iteration ${i}`, error);
        throw new VerificationError(
          `Z3 constraint generation failed: ${error instanceof Error ? error.message : String(error)}`
        );
      }

      // Phase 3: Z3 Verification
      logger.debug('Phase 3: Running Z3 solver');
      let z3Result: Z3Result;

      try {
        z3Result = await runZ3(z3Constraints, { timeout: 60000 });
        logger.info(`Z3 completed - Result: ${z3Result.result}`, {
          success: z3Result.success,
          constraintsChecked: z3Result.constraintsChecked.length,
        });
      } catch (error) {
        logger.error(`Z3 execution failed in iteration ${i}`, error);
        throw new VerificationError(
          `Z3 execution failed: ${error instanceof Error ? error.message : String(error)}`
        );
      }

      // Record this iteration
      const iterationDuration = Date.now() - iterationStart;
      const iterationRecord: IterationRecord = {
        iteration: i,
        code: currentCode,
        z3Constraints,
        z3Result: {
          ...z3Result,
          duration: iterationDuration,
        },
        feedback,
      };
      iterationHistory.push(iterationRecord);

      // Check if verification succeeded (unsat = no counter-examples = correct!)
      if (z3Result.success && z3Result.result === 'unsat') {
        const totalDuration = Date.now() - startTime;
        logger.info(`✓ Verification successful after ${i} iteration(s)!`, {
          totalDuration: `${(totalDuration / 1000).toFixed(2)}s`,
          constraintsChecked: z3Result.constraintsChecked.length,
        });

        const proofReport = generateProofReport(z3Result, spec);

        return {
          success: true,
          iterations: i,
          finalCode: currentCode,
          z3Constraints,
          proofReport,
          iterationHistory,
        };
      }

      // Phase 4: Extract counter-example and generate repair feedback
      logger.debug('Phase 4: Extracting counter-example and generating feedback');

      feedback = generateZ3RepairFeedback(z3Result, currentCode);

      logger.info(`Iteration ${i} failed, preparing repair for iteration ${i + 1}`, {
        result: z3Result.result,
        feedbackLength: feedback.length,
      });
    }

    // Max iterations reached without success
    const totalDuration = Date.now() - startTime;
    logger.warn(`✗ Max iterations (${maxIterations}) reached without verification`, {
      totalDuration: `${(totalDuration / 1000).toFixed(2)}s`,
    });

    return {
      success: false,
      iterations: maxIterations,
      error: `Max iterations (${maxIterations}) reached without finding a correct implementation.`,
      iterationHistory,
    };

  } catch (error) {
    // Catch any unexpected errors
    const totalDuration = Date.now() - startTime;
    logger.error('CEGIS loop (Z3) failed with unexpected error', {
      error,
      totalDuration: `${(totalDuration / 1000).toFixed(2)}s`,
    });

    return {
      success: false,
      iterations: iterationHistory.length,
      error: `CEGIS loop failed: ${error instanceof Error ? error.message : String(error)}`,
      iterationHistory,
    };
  }
}

