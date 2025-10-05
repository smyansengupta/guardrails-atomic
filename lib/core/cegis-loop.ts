import { Specification } from '@/lib/types/specification';
import {
  VerificationResult,
  IterationRecord,
  TLCResult,
  ProofReport
} from '@/lib/types/verification';
import { generateCode } from './code-generator';
import { generateTLAModule, tlaModuleToString, generateTLCConfig } from '@/lib/verification/tla-generator';
import { runTLC } from '@/lib/verification/tlc-runner';
import { parseCounterExample, generateRepairFeedback } from '@/lib/verification/counterexample-parser';
import { logger } from '@/lib/utils/logger';
import { VerificationError } from '@/lib/utils/errors';

/**
 * Generate a proof report from successful verification
 */
function generateProofReport(
  tlcResult: TLCResult,
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
    statesExplored: tlcResult.statesExplored,
    invariantsVerified: tlcResult.invariantsChecked,
    faultScenariosChecked,
    guarantees,
    timestamp: new Date().toISOString(),
    duration: tlcResult.duration || 0,
  };
}

/**
 * Main CEGIS loop: iteratively generate code, verify, and repair
 *
 * @param spec - The specification to verify
 * @param maxIterations - Maximum number of CEGIS iterations (default: 8)
 * @returns The verification result including final code and proof report
 *
 * The CEGIS loop works as follows:
 * 1. Generate TypeScript code from specification using LLM
 * 2. Translate specification to TLA+ formal model
 * 3. Run TLC model checker to verify all invariants
 * 4. If violations found, extract counterexample and generate repair feedback
 * 5. Use feedback to regenerate code (repair mode)
 * 6. Repeat until verified or max iterations reached
 */
export async function runCEGISLoop(
  spec: Specification,
  maxIterations: number = 8
): Promise<VerificationResult> {
  logger.info(`Starting CEGIS loop for spec: ${spec.name}`, { maxIterations });

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

      // Phase 2: TLA+ Generation
      logger.debug('Phase 2: Generating TLA+ specification');
      let tlaModule;
      let tlaSpec: string;
      let configFile: string;

      try {
        tlaModule = await generateTLAModule(spec);
        tlaSpec = tlaModuleToString(tlaModule);
        configFile = await generateTLCConfig(spec);
        logger.debug('TLA+ generation successful', {
          tlaLength: tlaSpec.length,
          configLength: configFile.length
        });
      } catch (error) {
        logger.error(`TLA+ generation failed in iteration ${i}`, error);
        throw new VerificationError(
          `TLA+ generation failed: ${error instanceof Error ? error.message : String(error)}`
        );
      }

      // Phase 3: TLC Verification
      logger.debug('Phase 3: Running TLC model checker');
      let tlcResult: TLCResult;

      try {
        tlcResult = await runTLC(tlaSpec, configFile);
        logger.info(`TLC completed - Success: ${tlcResult.success}`, {
          statesExplored: tlcResult.statesExplored,
          invariantsChecked: tlcResult.invariantsChecked.length,
        });
      } catch (error) {
        logger.error(`TLC execution failed in iteration ${i}`, error);
        throw new VerificationError(
          `TLC execution failed: ${error instanceof Error ? error.message : String(error)}`
        );
      }

      // Record this iteration
      const iterationDuration = Date.now() - iterationStart;
      const iterationRecord: IterationRecord = {
        iteration: i,
        code: currentCode,
        tlaSpec,
        tlcResult: {
          ...tlcResult,
          duration: iterationDuration,
        },
        feedback,
      };
      iterationHistory.push(iterationRecord);

      // Check if verification succeeded
      if (tlcResult.success) {
        const totalDuration = Date.now() - startTime;
        logger.info(`✓ Verification successful after ${i} iteration(s)!`, {
          totalDuration: `${(totalDuration / 1000).toFixed(2)}s`,
          statesExplored: tlcResult.statesExplored,
        });

        const proofReport = generateProofReport(tlcResult, spec);

        return {
          success: true,
          iterations: i,
          finalCode: currentCode,
          tlaSpec,
          proofReport,
          iterationHistory,
        };
      }

      // Phase 4: Extract counterexample and generate repair feedback
      logger.debug('Phase 4: Extracting counterexample and generating feedback');

      let repairFeedback: string;
      if (tlcResult.counterExample) {
        repairFeedback = generateRepairFeedback(tlcResult.counterExample);
        logger.debug('Counterexample parsed successfully', {
          violation: tlcResult.counterExample.violation.invariantName,
          scheduleLength: tlcResult.counterExample.schedule.length,
        });
      } else if (tlcResult.violations && tlcResult.violations.length > 0) {
        // Fallback: use violation messages directly
        repairFeedback = `Invariant violations detected:\n\n${
          tlcResult.violations.map(v =>
            `- ${v.invariantName}: ${v.message}`
          ).join('\n')
        }\n\nPlease fix the code to satisfy these invariants.`;
        logger.warn('No structured counterexample available, using violation messages');
      } else {
        // Fallback: use raw TLC output
        repairFeedback = `Verification failed but no specific counterexample was found.\n\nTLC Output:\n${tlcResult.output}`;
        logger.warn('No counterexample or violations found in TLC output');
      }

      // Include the previous code in the feedback for repair mode
      feedback = `ORIGINAL CODE:\n${currentCode}\n\n${repairFeedback}`;

      logger.info(`Iteration ${i} failed, preparing repair for iteration ${i + 1}`, {
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
      error: `Max iterations (${maxIterations}) reached without finding a correct implementation. Last violation: ${
        iterationHistory[iterationHistory.length - 1]?.tlcResult?.violations?.[0]?.invariantName || 'Unknown'
      }`,
      iterationHistory,
    };

  } catch (error) {
    // Catch any unexpected errors
    const totalDuration = Date.now() - startTime;
    logger.error('CEGIS loop failed with unexpected error', {
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
