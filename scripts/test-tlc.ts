/**
 * Manual test script for TLC runner
 * Run with: pnpm tsx scripts/test-tlc.ts
 */

import { readFile } from 'fs/promises';
import path from 'path';
import { runTLC, checkDockerAvailable } from '../lib/verification/tlc-runner';

async function main() {
  console.log('=== TLC Runner Manual Test ===\n');

  // Check Docker availability
  console.log('1. Checking Docker availability...');
  const dockerAvailable = await checkDockerAvailable();
  if (!dockerAvailable) {
    console.error('❌ Docker is not available. Please start Docker and try again.');
    process.exit(1);
  }
  console.log('✓ Docker is available\n');

  // Test 1: Simple counter (should pass)
  console.log('2. Testing with SimpleCounter.tla (should PASS)...');
  try {
    const simpleSpec = await readFile(
      path.join(process.cwd(), 'tests/fixtures/SimpleCounter.tla'),
      'utf-8'
    );
    const simpleConfig = await readFile(
      path.join(process.cwd(), 'tests/fixtures/SimpleCounter.cfg'),
      'utf-8'
    );

    const result1 = await runTLC(simpleSpec, simpleConfig);

    console.log(`Result: ${result1.success ? '✓ PASSED' : '✗ FAILED'}`);
    console.log(`States explored: ${result1.statesExplored}`);
    console.log(`Invariants checked: ${result1.invariantsChecked.join(', ')}`);
    console.log(`Duration: ${result1.duration}ms`);

    if (!result1.success) {
      console.log('Violations:', result1.violations);
    }
    console.log();
  } catch (error) {
    console.error('❌ Test 1 failed with error:', error);
    console.log();
  }

  // Test 2: Broken counter (should fail)
  console.log('3. Testing with BrokenCounter.tla (should FAIL with violation)...');
  try {
    const brokenSpec = await readFile(
      path.join(process.cwd(), 'tests/fixtures/BrokenCounter.tla'),
      'utf-8'
    );
    const brokenConfig = await readFile(
      path.join(process.cwd(), 'tests/fixtures/BrokenCounter.cfg'),
      'utf-8'
    );

    const result2 = await runTLC(brokenSpec, brokenConfig);

    console.log(`Result: ${result2.success ? '✓ PASSED (unexpected!)' : '✗ FAILED (expected)'}`);
    console.log(`States explored: ${result2.statesExplored}`);
    console.log(`Duration: ${result2.duration}ms`);

    if (result2.violations) {
      console.log(`Violations found: ${result2.violations.length}`);
      result2.violations.forEach((v, i) => {
        console.log(`  ${i + 1}. ${v.invariantName}: ${v.message}`);
      });
    }

    if (result2.counterExample) {
      console.log(`Counter-example with ${result2.counterExample.schedule.length} states`);
      console.log(`Suggested fix: ${result2.counterExample.suggestedFix}`);
    }
    console.log();
  } catch (error) {
    console.error('❌ Test 2 failed with error:', error);
    console.log();
  }

  console.log('=== Tests Complete ===');
}

main().catch(console.error);
