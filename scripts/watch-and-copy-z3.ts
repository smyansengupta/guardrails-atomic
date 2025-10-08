/**
 * Watch for .next directory changes and copy Z3 WASM files
 *
 * TODO: This is a temporary workaround. We need to brainstorm a better solution.
 *
 * The problem:
 * - z3-solver expects WASM files in specific locations
 * - Next.js bundles server code into .next/server/chunks/
 * - Z3 tries to load from .next/server/chunks/z3-built.wasm
 * - We need to ensure WASM files are available there
 *
 * Potential better solutions to explore:
 * 1. Configure Next.js webpack to properly handle WASM files (attempted in next.config.ts)
 * 2. Use Next.js static file serving from public/ with proper path configuration
 * 3. Modify z3-solver initialization to use custom WASM path
 * 4. Use a different Z3 binding that works better with Next.js
 * 5. Create a custom Next.js plugin for WASM handling
 */

import { watch } from 'fs';
import { exec } from 'child_process';
import { promisify } from 'util';

const execAsync = promisify(exec);

console.log('Watching for .next directory changes...');
console.log('Will copy Z3 WASM files when vendor chunks are rebuilt');

let copying = false;

const watcher = watch('.next', { recursive: true }, async (eventType, filename) => {
  // Only trigger on vendor-chunks changes
  if (filename && filename.includes('vendor-chunks') && !copying) {
    copying = true;
    console.log(`\nDetected change in ${filename}`);
    console.log('Copying Z3 WASM files...');

    try {
      await execAsync('tsx scripts/copy-z3-wasm.ts');
      console.log('✓ Z3 WASM files copied successfully\n');
    } catch (error) {
      console.error('✗ Failed to copy Z3 WASM files:', error);
    } finally {
      copying = false;
    }
  }
});

// Handle termination
process.on('SIGINT', () => {
  console.log('\nStopping watcher...');
  watcher.close();
  process.exit(0);
});

process.on('SIGTERM', () => {
  watcher.close();
  process.exit(0);
});
