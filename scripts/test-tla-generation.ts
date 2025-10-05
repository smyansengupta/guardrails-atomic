/**
 * Test script for TLA+ generation
 *
 * This script tests the TLA+ generator by:
 * 1. Loading an example spec (idempotent-write.yaml)
 * 2. Generating TLA+ module and config
 * 3. Writing to files
 * 4. Running TLC to verify
 */

import { readFile, writeFile } from 'fs/promises';
import path from 'path';
import { parseSpec } from '../lib/core/spec-parser';
import { generateTLAModule, tlaModuleToString, generateTLCConfig } from '../lib/verification/tla-generator';
import { runTLC } from '../lib/verification/tlc-runner';

async function testTLAGeneration() {
  console.log('=== TLA+ Generation Test ===\n');

  try {
    // 1. Load and parse spec
    console.log('1. Loading transfer.yaml...');
    const specPath = path.join(process.cwd(), 'templates', 'specs', 'transfer.yaml');
    const specYaml = await readFile(specPath, 'utf-8');
    console.log('YAML content:');
    console.log(specYaml);
    console.log('\nParsing...');
    const spec = parseSpec(specYaml);
    console.log(`✓ Loaded spec: ${spec.name}\n`);

    // 2. Generate TLA+ module
    console.log('2. Generating TLA+ module...');
    const tlaModule = await generateTLAModule(spec);
    const tlaSpec = tlaModuleToString(tlaModule);
    console.log(`✓ Generated TLA+ module (${tlaSpec.length} chars)\n`);

    // 3. Generate TLC config
    console.log('3. Generating TLC config...');
    const configFile = await generateTLCConfig(spec);
    console.log(`✓ Generated config file (${configFile.length} chars)\n`);

    // 4. Write to files for inspection
    const outputDir = path.join(process.cwd(), 'tla-output');
    const { mkdir } = await import('fs/promises');
    await mkdir(outputDir, { recursive: true });

    const tlaPath = path.join(outputDir, `${spec.name}.tla`);
    const cfgPath = path.join(outputDir, `${spec.name}.cfg`);

    await writeFile(tlaPath, tlaSpec);
    await writeFile(cfgPath, configFile);
    console.log(`4. Written files to ${outputDir}/\n`);

    console.log('Generated TLA+ spec:');
    console.log('-------------------');
    console.log(tlaSpec);
    console.log('\nGenerated config:');
    console.log('-------------------');
    console.log(configFile);
    console.log('');

    // 5. Try to run TLC
    console.log('5. Running TLC model checker...');
    const tlcResult = await runTLC(tlaSpec, configFile);

    if (tlcResult.success) {
      console.log('✅ TLC PASSED!');
      console.log(`   States explored: ${tlcResult.statesExplored}`);
      console.log(`   Invariants checked: ${tlcResult.invariantsChecked.join(', ')}`);
      console.log(`   Duration: ${tlcResult.duration}ms`);
    } else {
      console.log('❌ TLC FAILED');
      console.log('Violations:');
      tlcResult.violations?.forEach(v => {
        console.log(`   - ${v.invariantName}: ${v.message}`);
      });
      console.log('\nFull output:');
      console.log(tlcResult.output);
    }

  } catch (error) {
    console.error('❌ Test failed:', error);
    if (error instanceof Error) {
      console.error('Message:', error.message);
      console.error('Stack:', error.stack);
    }
    process.exit(1);
  }
}

testTLAGeneration();
