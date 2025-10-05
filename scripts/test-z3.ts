/**
 * Test script for Z3 verification
 * 
 * Usage:
 *   pnpm tsx scripts/test-z3.ts
 *   pnpm tsx scripts/test-z3.ts templates/specs/transfer.yaml
 */

import { readFile } from 'fs/promises';
import path from 'path';
import { parseSpec } from '../lib/core/spec-parser';
import { generateZ3Module, z3ModuleToString } from '../lib/verification/z3-generator';
import { runZ3 } from '../lib/verification/z3-runner';
import { runCEGISLoopZ3 } from '../lib/core/cegis-loop-z3';

const GREEN = '\x1b[32m';
const RED = '\x1b[31m';
const YELLOW = '\x1b[33m';
const BLUE = '\x1b[34m';
const RESET = '\x1b[0m';

async function testZ3Constraints() {
  console.log(`\n${BLUE}🚀 Testing Z3 Verification${RESET}\n`);

  // Get spec file from command line or use default
  const specFile = process.argv[2] || 'templates/specs/transfer.yaml';
  const specPath = path.resolve(process.cwd(), specFile);

  console.log(`${BLUE}📋 Loading spec:${RESET} ${specFile}`);

  // Step 1: Load and parse spec
  const specYaml = await readFile(specPath, 'utf-8');
  const spec = parseSpec(specYaml);
  console.log(`${GREEN}✅ Spec parsed successfully${RESET}`);
  console.log(`   Name: ${spec.name}`);
  console.log(`   Preconditions: ${spec.preconditions.length}`);
  console.log(`   Postconditions: ${spec.postconditions.length}`);
  console.log(`   Invariants: ${spec.invariants.map(i => i.type).join(', ')}`);

  // Step 2: Generate Z3 constraints
  console.log(`\n${BLUE}⚙️  Generating Z3 constraints...${RESET}`);
  const z3Module = generateZ3Module(spec);
  const z3Constraints = z3ModuleToString(z3Module);
  
  console.log(`${GREEN}✅ Z3 constraints generated${RESET} (${z3Constraints.length} chars)`);
  console.log(`   Constants: ${z3Module.constants.length}`);
  console.log(`   Constraints: ${z3Module.constraints.length}`);
  
  // Show generated constraints
  console.log(`\n${YELLOW}📄 Generated SMT-LIB:${RESET}`);
  console.log('─'.repeat(60));
  console.log(z3Constraints);
  console.log('─'.repeat(60));

  // Step 3: Run Z3
  console.log(`\n${BLUE}🔍 Running Z3 solver...${RESET}`);
  try {
    const z3Result = await runZ3(z3Constraints, { timeout: 60000 });
    
    if (z3Result.result === 'unsat') {
      console.log(`${GREEN}✅ Z3 result: unsat (verification successful!)${RESET}`);
      console.log(`   Constraints checked: ${z3Result.constraintsChecked.length}`);
      console.log(`   Duration: ${z3Result.duration}ms`);
      console.log(`\n${GREEN}🎉 The specification is CORRECT!${RESET}`);
    } else if (z3Result.result === 'sat') {
      console.log(`${RED}❌ Z3 result: sat (counter-example found!)${RESET}`);
      console.log(`   Constraints checked: ${z3Result.constraintsChecked.length}`);
      console.log(`   Duration: ${z3Result.duration}ms`);
      
      if (z3Result.model) {
        console.log(`\n${YELLOW}📊 Counter-example model:${RESET}`);
        for (const [varName, value] of Object.entries(z3Result.model.variables)) {
          console.log(`   ${varName} = ${value.value}`);
        }
      }
      
      if (z3Result.counterExample) {
        console.log(`\n${YELLOW}💡 Suggested fix:${RESET}`);
        console.log(z3Result.counterExample.suggestedFix);
      }
    } else {
      console.log(`${YELLOW}⚠️  Z3 result: unknown${RESET}`);
      console.log(`   Z3 couldn't determine satisfiability`);
      console.log(`   This might be due to timeout or complexity`);
    }
  } catch (error) {
    console.error(`${RED}❌ Z3 execution failed:${RESET}`, error);
    throw error;
  }
}

async function testFullCEGIS() {
  console.log(`\n${BLUE}🔄 Testing Full CEGIS Loop with Z3${RESET}\n`);

  const specFile = process.argv[2] || 'templates/specs/transfer.yaml';
  const specPath = path.resolve(process.cwd(), specFile);

  console.log(`${BLUE}📋 Loading spec:${RESET} ${specFile}`);

  const specYaml = await readFile(specPath, 'utf-8');
  const spec = parseSpec(specYaml);
  
  console.log(`${GREEN}✅ Spec parsed${RESET}`);
  console.log(`\n${BLUE}🔁 Running CEGIS loop (max 3 iterations)...${RESET}\n`);

  try {
    const result = await runCEGISLoopZ3(spec, 3);

    if (result.success) {
      console.log(`\n${GREEN}✅ CEGIS Loop Successful!${RESET}`);
      console.log(`   Iterations: ${result.iterations}`);
      console.log(`   Constraints checked: ${result.proofReport?.constraintsChecked}`);
      console.log(`\n${YELLOW}📝 Generated Code:${RESET}`);
      console.log('─'.repeat(60));
      console.log(result.finalCode);
      console.log('─'.repeat(60));
      
      if (result.proofReport) {
        console.log(`\n${GREEN}🎉 Proof Report:${RESET}`);
        console.log(`   Invariants Verified: ${result.proofReport.invariantsVerified.join(', ')}`);
        console.log(`   Fault Scenarios: ${result.proofReport.faultScenariosChecked.join(', ')}`);
        console.log(`\n${GREEN}✨ Guarantees:${RESET}`);
        result.proofReport.guarantees.forEach((g, i) => {
          console.log(`   ${i + 1}. ${g}`);
        });
      }
    } else {
      console.log(`\n${RED}❌ CEGIS Loop Failed${RESET}`);
      console.log(`   Iterations: ${result.iterations}`);
      console.log(`   Error: ${result.error}`);
      
      if (result.iterationHistory && result.iterationHistory.length > 0) {
        const lastIter = result.iterationHistory[result.iterationHistory.length - 1];
        console.log(`\n${YELLOW}Last iteration details:${RESET}`);
        console.log(`   Z3 result: ${lastIter.z3Result?.result}`);
        if (lastIter.z3Result?.counterExample) {
          console.log(`   Counter-example: ${lastIter.z3Result.counterExample.trace.slice(0, 200)}...`);
        }
      }
    }
  } catch (error) {
    console.error(`${RED}❌ CEGIS loop failed:${RESET}`, error);
    throw error;
  }
}

// Main
async function main() {
  const mode = process.env.MODE || 'constraints';

  try {
    if (mode === 'cegis') {
      await testFullCEGIS();
    } else {
      await testZ3Constraints();
    }
    
    console.log(`\n${GREEN}✅ Test completed successfully${RESET}\n`);
  } catch (error) {
    console.error(`\n${RED}❌ Test failed:${RESET}`, error);
    process.exit(1);
  }
}

main();

