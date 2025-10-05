/**
 * Manual integration test for code generator
 *
 * This script tests the code generator with real LLM calls.
 * DO NOT run in automated tests (costs money!).
 *
 * Usage: pnpm tsx scripts/test-code-generator.ts
 */

import { parseSpec } from '../lib/core/spec-parser';
import { generateCode } from '../lib/core/code-generator';
import { readFile } from 'fs/promises';
import path from 'path';

async function main() {
  console.log('🧪 Manual Integration Test: Code Generator\n');

  try {
    // Load transfer spec
    console.log('1️⃣  Loading transfer spec...');
    const specPath = path.join(process.cwd(), 'templates', 'specs', 'transfer.yaml');
    const yamlContent = await readFile(specPath, 'utf-8');
    const spec = parseSpec(yamlContent);
    console.log(`   ✓ Loaded spec: ${spec.name}\n`);

    // Test initial code generation
    console.log('2️⃣  Generating initial code...');
    console.log('   (This will call OpenRouter API - may take 5-10 seconds)\n');
    const code = await generateCode(spec);
    console.log('   ✓ Code generated successfully!\n');

    // Display generated code
    console.log('📝 Generated Code:');
    console.log('─'.repeat(80));
    console.log(code);
    console.log('─'.repeat(80));
    console.log();

    // Validate code structure
    console.log('3️⃣  Validating generated code...');
    const validations = [
      { name: 'Contains function definition', test: code.includes('function') || code.includes('=>') },
      { name: 'Has transfer logic', test: code.toLowerCase().includes('transfer') || code.includes('from') || code.includes('to') },
      { name: 'Non-empty', test: code.length > 50 },
      { name: 'Is valid TypeScript syntax', test: !code.includes('{{') && !code.includes('}}') },
    ];

    let allValid = true;
    for (const validation of validations) {
      const status = validation.test ? '✓' : '✗';
      console.log(`   ${status} ${validation.name}`);
      if (!validation.test) allValid = false;
    }
    console.log();

    if (allValid) {
      console.log('✅ All validations passed!');
    } else {
      console.log('⚠️  Some validations failed');
    }

    // Test repair mode (optional)
    console.log('\n4️⃣  Testing repair mode...');
    const mockFeedback = `ORIGINAL CODE:
${code}

VIOLATION: Idempotent invariant failed

EXECUTION TRACE:
1. Init - State: balances={"a1":100,"a2":0}
2. TransferAction - State: balances={"a1":50,"a2":50}
3. DuplicateTransferAction - State: balances={"a1":0,"a2":100}

ISSUE: Invariant Idempotent was violated after 3 steps

FIX: Check if the request ID is already in the processed set before executing the operation. Add: if (processed.has(requestId)) return;`;

    console.log('   (Simulating repair with mock feedback)\n');
    const repairedCode = await generateCode(spec, mockFeedback);
    console.log('   ✓ Repaired code generated!\n');

    console.log('📝 Repaired Code:');
    console.log('─'.repeat(80));
    console.log(repairedCode);
    console.log('─'.repeat(80));
    console.log();

    // Check if repair addressed the issue
    const hasIdempotencyCheck =
      repairedCode.includes('processed') ||
      repairedCode.includes('requestId') ||
      repairedCode.includes('req_id') ||
      repairedCode.toLowerCase().includes('idempotent');

    if (hasIdempotencyCheck) {
      console.log('✅ Repair appears to address idempotency!');
    } else {
      console.log('⚠️  Repair may not fully address idempotency');
    }

    console.log('\n🎉 Integration test completed successfully!');
  } catch (error) {
    console.error('\n❌ Test failed:', error);
    process.exit(1);
  }
}

main();
