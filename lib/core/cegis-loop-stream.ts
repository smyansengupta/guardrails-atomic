import { Specification } from '@/lib/types/specification';
import {
  VerificationResult,
  IterationRecord,
  TLCResult,
  ProofReport,
} from '@/lib/types/verification';
import { VerificationEvent } from '@/lib/types/api';
import { generateCode } from './code-generator';
import { generateTLAModule, tlaModuleToString, generateTLCConfig } from '@/lib/verification/tla-generator';
import { runTLC } from '@/lib/verification/tlc-runner';
import { generateRepairFeedback } from '@/lib/verification/counterexample-parser';
import { logger } from '@/lib/utils/logger';
import { VerificationError } from '@/lib/utils/errors';

/**
 * Runs the CEGIS loop with real-time event emission for SSE streaming.
 *
 * This is the event-emitting version of runCEGISLoop() that supports
 * real-time progress updates via Server-Sent Events.
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

  logger.info(`Starting CEGIS loop with SSE events (max ${maxIterations} iterations)`);

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

      // 2. TLA+ GENERATION PHASE
      emitEvent({
        type: 'progress',
        phase: 'generating_tla',
        message: 'Translating specification to TLA+...',
        timestamp: new Date().toISOString(),
      });

      let tlaModule;
      let tlaSpec: string;
      let configFile: string;

      try {
        tlaModule = await generateTLAModule(spec);
        tlaSpec = tlaModuleToString(tlaModule);
        configFile = await generateTLCConfig(spec);

        emitEvent({
          type: 'tla_generated',
          iteration: i,
          tlaLength: tlaSpec.length,
          timestamp: new Date().toISOString(),
        });

        logger.info(`Generated TLA+ spec: ${tlaSpec.length} characters`);
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : String(error);
        logger.error(`TLA+ generation failed in iteration ${i}: ${errorMessage}`);

        emitEvent({
          type: 'error',
          phase: 'generating_tla',
          message: `TLA+ generation failed: ${errorMessage}. This feature is still in development.`,
          timestamp: new Date().toISOString(),
        });

        // Graceful degradation: return partial result
        return {
          success: false,
          iterations: i,
          finalCode: currentCode,
          error: `TLA+ generation not yet implemented: ${errorMessage}`,
          iterationHistory,
        };
      }

      // 3. TLC VERIFICATION PHASE
      emitEvent({
        type: 'tlc_start',
        iteration: i,
        timestamp: new Date().toISOString(),
      });

      emitEvent({
        type: 'progress',
        phase: 'running_tlc',
        message: 'Running TLC model checker...',
        timestamp: new Date().toISOString(),
      });

      let tlcResult: TLCResult;

      try {
        tlcResult = await runTLC(tlaSpec, configFile);

        const tlcDuration = Date.now() - iterationStartTime;

        emitEvent({
          type: 'tlc_complete',
          iteration: i,
          success: tlcResult.success,
          statesExplored: tlcResult.statesExplored || 0,
          duration: tlcDuration,
          timestamp: new Date().toISOString(),
        });

        logger.info(
          `TLC completed: ${tlcResult.success ? 'VERIFIED' : 'VIOLATION'}, ` +
          `${tlcResult.statesExplored || 0} states explored`
        );
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : String(error);
        logger.error(`TLC execution failed in iteration ${i}: ${errorMessage}`);

        emitEvent({
          type: 'error',
          phase: 'running_tlc',
          message: `TLC execution failed: ${errorMessage}`,
          timestamp: new Date().toISOString(),
        });

        throw new VerificationError(`TLC execution failed: ${errorMessage}`);
      }

      // Record iteration
      iterationHistory.push({
        iteration: i,
        code: currentCode,
        tlaSpec,
        tlcResult,
        feedback,
      });

      // 4. ANALYZE RESULTS PHASE
      emitEvent({
        type: 'progress',
        phase: 'analyzing_results',
        message: tlcResult.success ? 'Verification successful!' : 'Analyzing counterexample...',
        timestamp: new Date().toISOString(),
      });

      emitEvent({
        type: 'iteration_complete',
        iteration: i,
        success: tlcResult.success,
        statesExplored: tlcResult.statesExplored || 0,
        violationFound: !tlcResult.success,
        timestamp: new Date().toISOString(),
      });

      // 5. CHECK VERIFICATION SUCCESS
      if (tlcResult.success) {
        const proofReport = generateProofReport(spec, tlcResult, i);

        const result: VerificationResult = {
          success: true,
          iterations: i,
          finalCode: currentCode,
          tlaSpec,
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

        logger.info(`CEGIS loop succeeded in ${i} iteration(s)`);
        return result;
      }

      // 6. EXTRACT COUNTEREXAMPLE AND PREPARE REPAIR
      if (tlcResult.counterExample) {
        feedback = `ORIGINAL CODE:\n${currentCode}\n\n${generateRepairFeedback(tlcResult.counterExample)}`;
        logger.info(`Iteration ${i} failed, preparing repair with counterexample feedback`);
      } else {
        // Fallback: use raw TLC output
        feedback = `ORIGINAL CODE:\n${currentCode}\n\nTLC Output:\n${tlcResult.output || 'No output available'}`;
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
 * Generates a proof report from successful TLC verification.
 */
function generateProofReport(
  spec: Specification,
  tlcResult: TLCResult,
  iterations: number
): ProofReport {
  const invariantsVerified = tlcResult.invariantsChecked || spec.invariants.map(inv => inv.type);

  return {
    statesExplored: tlcResult.statesExplored || 0,
    invariantsVerified,
    faultScenariosChecked: [
      `Delivery: ${spec.faultModel.delivery}`,
      spec.faultModel.reorder ? 'Message reordering' : null,
      spec.faultModel.crash_restart ? 'Crash/restart' : null,
      spec.faultModel.network_partition ? 'Network partition' : null,
    ].filter(Boolean) as string[],
    guarantees: invariantsVerified.map(inv => `${inv} property verified under ${spec.faultModel.delivery} delivery`),
    timestamp: new Date().toISOString(),
    duration: tlcResult.duration || 0,
  };
}
