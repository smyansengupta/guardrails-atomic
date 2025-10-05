import { Specification } from '@/lib/types/specification';
import {
  VerificationResult,
  IterationRecord,
  Z3Result,
  ProofReport,
} from '@/lib/types/verification';
import { VerificationEvent } from '@/lib/types/api';
import { generateCode } from './code-generator';
import { generateZ3Module, z3ModuleToString, generateZ3Config } from '@/lib/verification/z3-generator';
import { runZ3 } from '@/lib/verification/z3-runner';
import { logger } from '@/lib/utils/logger';
import { VerificationError } from '@/lib/utils/errors';

/**
 * Runs the CEGIS loop with real-time event emission for SSE streaming.
 *
 * This is the event-emitting version of runCEGISLoop() that supports
 * real-time progress updates via Server-Sent Events.
 * 
 * Uses Z3 SMT solver for formal verification.
 *
 * @param spec - The parsed specification
 * @param maxIterations - Maximum number of CEGIS iterations (default: 8)
 * @param emitEvent - Callback to emit verification events
 * @returns Promise resolving to the verification result
 */
export async function runCEGISLoopWithEvents(
  spec: Specification,
  maxIterations: number = 8,
  emitEvent: (event: VerificationEvent) => void
): Promise<VerificationResult> {
  const iterationHistory: IterationRecord[] = [];
  let currentCode: string | null = null;
  let feedback: string | undefined = undefined;

  logger.info(`Starting CEGIS loop (Z3) with SSE events (max ${maxIterations} iterations)`);

  // Emit parsing phase
  emitEvent({
    type: 'progress',
    phase: 'parsing',
    message: `Parsed specification: ${spec.name}`,
    timestamp: new Date().toISOString(),
  });

  try {
    for (let i = 1; i <= maxIterations; i++) {
      const iterationStartTime = Date.now();

      // Emit iteration start
      emitEvent({
        type: 'iteration_start',
        iteration: i,
        maxIterations,
        isRepair: !!feedback,
        timestamp: new Date().toISOString(),
      });

      logger.info(`CEGIS iteration ${i}/${maxIterations}${feedback ? ' (repair mode)' : ''}`);

      // 1. CODE GENERATION PHASE
      emitEvent({
        type: 'progress',
        phase: 'generating_code',
        message: feedback ? 'Repairing code based on counterexample...' : 'Generating initial code...',
        timestamp: new Date().toISOString(),
      });

      try {
        currentCode = await generateCode(spec, feedback);

        emitEvent({
          type: 'code_generated',
          iteration: i,
          codeLength: currentCode.length,
          preview: currentCode.slice(0, 100),
          timestamp: new Date().toISOString(),
        });

        logger.info(`Generated code: ${currentCode.length} characters`);
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : String(error);
        logger.error(`Code generation failed in iteration ${i}: ${errorMessage}`);

        emitEvent({
          type: 'error',
          phase: 'generating_code',
          message: `Code generation failed: ${errorMessage}`,
          timestamp: new Date().toISOString(),
        });

        throw new VerificationError(`Code generation failed: ${errorMessage}`);
      }

      // 2. Z3 CONSTRAINT GENERATION PHASE
      emitEvent({
        type: 'progress',
        phase: 'generating_tla',
        message: 'Generating Z3 SMT constraints...',
        timestamp: new Date().toISOString(),
      });

      let z3Module;
      let z3Constraints: string;
      let configFile: string;

      try {
        z3Module = generateZ3Module(spec);
        z3Constraints = z3ModuleToString(z3Module);
        configFile = generateZ3Config(spec);

        emitEvent({
          type: 'tla_generated',
          iteration: i,
          tlaLength: z3Constraints.length,
          timestamp: new Date().toISOString(),
        });

        logger.info(`Generated Z3 constraints: ${z3Constraints.length} characters`);
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : String(error);
        logger.error(`Z3 constraint generation failed in iteration ${i}: ${errorMessage}`);

        emitEvent({
          type: 'error',
          phase: 'generating_tla',
          message: `Z3 constraint generation failed: ${errorMessage}`,
          timestamp: new Date().toISOString(),
        });

        // Graceful degradation: return partial result
        return {
          success: false,
          iterations: i,
          finalCode: currentCode,
          error: `Z3 constraint generation failed: ${errorMessage}`,
          iterationHistory,
        };
      }

      // 3. Z3 VERIFICATION PHASE
      emitEvent({
        type: 'tlc_start',
        iteration: i,
        timestamp: new Date().toISOString(),
      });

      emitEvent({
        type: 'progress',
        phase: 'running_tlc',
        message: 'Running Z3 SMT solver...',
        timestamp: new Date().toISOString(),
      });

      let z3Result: Z3Result;

      try {
        z3Result = await runZ3(z3Constraints, { timeout: 60000 });

        const z3Duration = Date.now() - iterationStartTime;

        emitEvent({
          type: 'tlc_complete',
          iteration: i,
          success: z3Result.success && z3Result.result === 'unsat',
          statesExplored: 0, // Z3 doesn't count states like TLC
          duration: z3Duration,
          timestamp: new Date().toISOString(),
        });

        logger.info(
          `Z3 completed: ${z3Result.result}, ` +
          `${z3Result.constraintsChecked.length} constraints checked`
        );
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : String(error);
        logger.error(`Z3 execution failed in iteration ${i}: ${errorMessage}`);

        emitEvent({
          type: 'error',
          phase: 'running_tlc',
          message: `Z3 execution failed: ${errorMessage}`,
          timestamp: new Date().toISOString(),
        });

        throw new VerificationError(`Z3 execution failed: ${errorMessage}`);
      }

      // Record iteration
      iterationHistory.push({
        iteration: i,
        code: currentCode,
        z3Constraints,
        z3Result,
        feedback,
      });

      // 4. ANALYZE RESULTS PHASE
      const isVerified = z3Result.success && z3Result.result === 'unsat';
      
      emitEvent({
        type: 'progress',
        phase: 'analyzing_results',
        message: isVerified ? 'Verification successful!' : 'Analyzing counterexample...',
        timestamp: new Date().toISOString(),
      });

      emitEvent({
        type: 'iteration_complete',
        iteration: i,
        success: isVerified,
        statesExplored: 0,
        violationFound: !isVerified,
        timestamp: new Date().toISOString(),
      });

      // 5. CHECK VERIFICATION SUCCESS
      if (isVerified) {
        const proofReport = generateProofReport(z3Result, spec);

        const result: VerificationResult = {
          success: true,
          iterations: i,
          finalCode: currentCode,
          z3Constraints,
          proofReport,
          iterationHistory,
        };

        emitEvent({
          type: 'verification_complete',
          success: true,
          iterations: i,
          result,
          timestamp: new Date().toISOString(),
        });

        logger.info(`CEGIS loop (Z3) succeeded in ${i} iteration(s)`);
        return result;
      }

      // 6. EXTRACT COUNTEREXAMPLE AND PREPARE REPAIR
      if (z3Result.counterExample) {
        feedback = generateZ3RepairFeedback(z3Result, currentCode);
        logger.info(`Iteration ${i} failed, preparing repair with Z3 counterexample feedback`);
      } else {
        // Fallback: use raw Z3 output
        feedback = `ORIGINAL CODE:\n${currentCode}\n\nZ3 Result: ${z3Result.result}\nOutput:\n${z3Result.output || 'No output available'}`;
        logger.warn(`Iteration ${i} failed, no structured counterexample found`);
      }
    }

    // Max iterations reached without success
    const result: VerificationResult = {
      success: false,
      iterations: maxIterations,
      error: `Verification failed after ${maxIterations} iterations. Unable to find correct implementation.`,
      iterationHistory,
    };

    emitEvent({
      type: 'verification_complete',
      success: false,
      iterations: maxIterations,
      result,
      timestamp: new Date().toISOString(),
    });

    logger.warn(`CEGIS loop failed: max iterations (${maxIterations}) reached`);
    return result;

  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : String(error);
    logger.error(`CEGIS loop error: ${errorMessage}`);

    emitEvent({
      type: 'error',
      phase: 'unknown',
      message: `Critical error: ${errorMessage}`,
      timestamp: new Date().toISOString(),
    });

    throw error;
  }
}

/**
 * Generates a proof report from successful Z3 verification.
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
    return `ORIGINAL CODE:\n${currentCode}\n\nZ3 found violations but no detailed counter-example is available.\n\nPlease review the code and fix the invariant violations.`;
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
