import { TLCResult, InvariantViolation } from '@/lib/types/verification';
import { TLCExecutionError } from '@/lib/utils/errors';
import { parseCounterExample, parseViolations } from './counterexample-parser';
import { logger } from '@/lib/utils/logger';
import { exec } from 'child_process';
import { promisify } from 'util';
import { writeFile, mkdir, rm } from 'fs/promises';
import path from 'path';
import os from 'os';

const execAsync = promisify(exec);

/**
 * Parse TLC output to extract state exploration metrics
 */
function parseStateMetrics(output: string): { statesExplored: number; distinctStates: number } {
  let statesExplored = 0;
  let distinctStates = 0;

  // Look for patterns like "X states generated" or "X distinct states found"
  const generatedMatch = output.match(/(\d+)\s+states?\s+generated/i);
  if (generatedMatch) {
    statesExplored = parseInt(generatedMatch[1], 10);
  }

  const distinctMatch = output.match(/(\d+)\s+distinct\s+states?\s+found/i);
  if (distinctMatch) {
    distinctStates = parseInt(distinctMatch[1], 10);
  }

  return { statesExplored: statesExplored || distinctStates, distinctStates };
}

/**
 * Extract checked invariants from TLC output
 */
function extractInvariants(output: string): string[] {
  const invariants: string[] = [];

  // Look for lines like "Invariant TypeOK is valid" or "Checking invariant TypeOK"
  const invariantMatches = output.matchAll(/(?:Invariant|Checking invariant)\s+(\w+)/gi);

  for (const match of invariantMatches) {
    const invName = match[1];
    if (invName && !invariants.includes(invName)) {
      invariants.push(invName);
    }
  }

  return invariants;
}

/**
 * Check if TLC output indicates success
 */
function isSuccess(output: string): boolean {
  // Success indicators
  const successPatterns = [
    /Model checking completed\./i,
    /No errors? has been found/i,
    /Finished in/i,
  ];

  // Failure indicators
  const failurePatterns = [
    /Error:/i,
    /Invariant .* is violated/i,
    /violated/i,
    /Deadlock reached/i,
  ];

  // Check for failures first (higher priority)
  for (const pattern of failurePatterns) {
    if (pattern.test(output)) {
      return false;
    }
  }

  // Then check for success
  for (const pattern of successPatterns) {
    if (pattern.test(output)) {
      return true;
    }
  }

  // If neither found, assume failure for safety
  return false;
}

/**
 * Build the Docker image if it doesn't exist
 */
async function ensureDockerImage(): Promise<void> {
  const imageName = process.env.TLC_DOCKER_IMAGE ?? 'guardrails-tlc';
  try {
    // Check if image exists
    const { stdout } = await execAsync(`docker images -q ${imageName}`);

    if (!stdout.trim()) {
      logger.info('TLC Docker image not found, building...');
      const dockerfilePath = process.env.TLC_DOCKER_CONTEXT ?? path.join(process.cwd(), 'docker', 'tlc');

      await execAsync(`docker build -t ${imageName} "${dockerfilePath}"`, {
        timeout: 120000, // 2 minutes for build
      });

      logger.info('TLC Docker image built successfully');
    }
  } catch (error) {
    throw new TLCExecutionError(
      `Failed to build Docker image: ${error instanceof Error ? error.message : String(error)}`
    );
  }
}

/**
 * Execute TLC model checker via Docker
 *
 * @param tlaSpec - The TLA+ specification as a string
 * @param configFile - The TLC configuration file content
 * @returns TLC execution results including violations and counterexamples
 *
 * Implementation:
 * 1. Create temporary directory for TLA+ files
 * 2. Write spec and config files
 * 3. Run TLC in Docker container with volume mount
 * 4. Parse output for results
 * 5. Extract counterexamples if violations found
 * 6. Clean up temporary files
 */
export async function runTLC(
  tlaSpec: string,
  configFile: string
): Promise<TLCResult> {
  const startTime = Date.now();
  let workDir: string | null = null;

  try {
    // Ensure Docker image exists
    await ensureDockerImage();

    // Create unique temporary directory
    const timestamp = Date.now();
    const randomId = Math.random().toString(36).substring(7);
    const sharedDir = process.env.TLC_SHARED_DIR;
    const containerWorkdir = process.env.TLC_CONTAINER_WORKDIR ?? '/workspace';
    const volumeName = process.env.TLC_DOCKER_VOLUME;
    const imageName = process.env.TLC_DOCKER_IMAGE ?? 'guardrails-tlc';
    const usingNamedVolume = Boolean(volumeName && sharedDir);

    const baseWorkspace = usingNamedVolume ? path.resolve(sharedDir!) : os.tmpdir();
    workDir = path.join(baseWorkspace, `tla-${timestamp}-${randomId}`);

    await mkdir(workDir, { recursive: true });
    logger.debug(`Created TLC workspace: ${workDir}`);

    // Extract module name from TLA+ spec
    // TLA+ modules must have: "---- MODULE ModuleName ----"
    const moduleMatch = tlaSpec.match(/----\s*MODULE\s+(\w+)\s*----/);
    const moduleName = moduleMatch ? moduleMatch[1] : 'Spec';

    // Write TLA+ spec and config files
    const specPath = path.join(workDir, `${moduleName}.tla`);
    const cfgPath = path.join(workDir, `${moduleName}.cfg`);

    await writeFile(specPath, tlaSpec, 'utf-8');
    await writeFile(cfgPath, configFile, 'utf-8');
    logger.debug(`Wrote TLA+ spec and config files for module: ${moduleName}`);

    // Run TLC in Docker container
    // Mount the work directory and run TLC on the spec
    let dockerCommand: string;

    if (usingNamedVolume) {
      const relativeDir = path.basename(workDir);
      const workdirInContainer = path.posix.join(
        containerWorkdir.replace(/\\/g, '/'),
        relativeDir
      );

      dockerCommand = [
        'docker run --rm',
        `-v ${volumeName}:${containerWorkdir}`,
        `--workdir ${workdirInContainer}`,
        imageName,
        '-config', `${moduleName}.cfg`,
        `${moduleName}.tla`,
      ].join(' ');
    } else {
      const containerMountPath = '/workspace';
      dockerCommand = [
        'docker run --rm',
        `-v "${workDir}:${containerMountPath}"`,
        `--workdir ${containerMountPath}`,
        imageName,
        '-config', `${moduleName}.cfg`,
        `${moduleName}.tla`,
      ].join(' ');
    }

    logger.debug(`Executing TLC: ${dockerCommand}`);

    let stdout = '';
    let stderr = '';
    let tlcExitCode = 0;

    try {
      const { stdout: out, stderr: err } = await execAsync(dockerCommand, {
        timeout: 60000, // 60 second timeout
        maxBuffer: 10 * 1024 * 1024, // 10MB buffer for large outputs
      });
      stdout = out;
      stderr = err;
    } catch (error: any) {
      // TLC may exit with non-zero code even for valid violations
      stdout = error.stdout || '';
      stderr = error.stderr || '';
      tlcExitCode = error.code || 1;

      // Only throw if it's a real execution error (not a TLC violation)
      if (!stdout && !stderr) {
        throw error;
      }
    }

    const output = stdout + '\n' + stderr;
    const duration = Date.now() - startTime;

    logger.debug('TLC execution completed', {
      exitCode: tlcExitCode,
      duration: `${duration}ms`,
      outputLength: output.length,
    });

    // Parse output
    const success = isSuccess(output);
    const { statesExplored } = parseStateMetrics(output);
    const invariantsChecked = extractInvariants(output);

    // Build result
    const result: TLCResult = {
      success,
      statesExplored,
      invariantsChecked,
      output,
      duration,
    };

    if (!success) {
      // Parse violations and counterexamples
      try {
        const violations = parseViolations(output);
        result.violations = violations;

        const counterExample = parseCounterExample(output);
        if (counterExample) {
          result.counterExample = counterExample;
        }
      } catch (parseError) {
        logger.warn('Failed to parse counterexample from TLC output', parseError);
        // Continue with basic violation info
        result.violations = [{
          invariantName: 'Unknown',
          message: 'Failed to parse violation details',
        }];
      }
    }

    return result;

  } catch (error) {
    const duration = Date.now() - startTime;

    logger.error('TLC execution failed', {
      error,
      duration: `${duration}ms`,
    });

    if (error instanceof TLCExecutionError) {
      throw error;
    }

    throw new TLCExecutionError(
      `TLC execution failed: ${error instanceof Error ? error.message : String(error)}`,
      error instanceof Error ? error.message : undefined
    );
  } finally {
    // Clean up temporary files
    if (workDir) {
      try {
        await rm(workDir, { recursive: true, force: true });
        logger.debug(`Cleaned up workspace: ${workDir}`);
      } catch (cleanupError) {
        logger.warn(`Failed to clean up workspace ${workDir}:`, cleanupError);
      }
    }
  }
}

/**
 * Check if Docker is available and running
 */
export async function checkDockerAvailable(): Promise<boolean> {
  try {
    await execAsync('docker version', { timeout: 5000 });
    return true;
  } catch (error) {
    return false;
  }
}
