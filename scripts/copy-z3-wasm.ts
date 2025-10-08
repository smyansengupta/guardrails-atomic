#!/usr/bin/env tsx
/**
 * Copy Z3 WASM files to public directory
 *
 * This ensures z3-solver can find its WASM files in Next.js builds.
 */

import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const sourceDir = path.join(__dirname, '..', 'node_modules', 'z3-solver', 'build');
const publicDir = path.join(__dirname, '..', 'public', 'z3');
const nextServerVendorDir = path.join(__dirname, '..', '.next', 'server', 'vendor-chunks');
const nextServerChunksDir = path.join(__dirname, '..', '.next', 'server', 'chunks');

console.log('📦 Setting up Z3 WASM files...');

// Create public/z3 directory
if (!fs.existsSync(publicDir)) {
  fs.mkdirSync(publicDir, { recursive: true });
  console.log('✓ Created public/z3 directory');
}

// Create .next/server directories if they exist (for running builds)
const nextServerDirs = [nextServerVendorDir, nextServerChunksDir];
if (fs.existsSync(path.join(__dirname, '..', '.next', 'server'))) {
  for (const dir of nextServerDirs) {
    if (!fs.existsSync(dir)) {
      fs.mkdirSync(dir, { recursive: true });
    }
  }
  console.log('✓ Found .next/server directory');
}

// Check if source directory exists
if (!fs.existsSync(sourceDir)) {
  console.warn('⚠️  Z3 source directory not found:', sourceDir);
  console.warn('   This is expected if z3-solver is not installed yet.');
  process.exit(0);
}

// Copy all WASM and supporting files
try {
  const files = fs.readdirSync(sourceDir);
  let copiedCount = 0;

  for (const file of files) {
    if (file.endsWith('.wasm') || file.endsWith('.js') || file.endsWith('.worker.js')) {
      const sourcePath = path.join(sourceDir, file);

      // Copy to public directory
      const publicDestPath = path.join(publicDir, file);
      fs.copyFileSync(sourcePath, publicDestPath);

      // Also copy to .next/server directories if they exist
      for (const destDir of [nextServerVendorDir, nextServerChunksDir]) {
        if (fs.existsSync(destDir)) {
          const nextDestPath = path.join(destDir, file);
          fs.copyFileSync(sourcePath, nextDestPath);
        }
      }

      copiedCount++;
      console.log(`✓ Copied ${file}`);
    }
  }

  if (copiedCount === 0) {
    console.warn('⚠️  No WASM files found in', sourceDir);
  } else {
    console.log(`✅ Successfully copied ${copiedCount} file(s) to public/z3/`);
    if (fs.existsSync(nextServerVendorDir) || fs.existsSync(nextServerChunksDir)) {
      console.log(`✅ Also copied to .next/server/ directories`);
    }
  }
} catch (error) {
  const errorMessage = error instanceof Error ? error.message : String(error);
  console.error('❌ Error copying Z3 files:', errorMessage);
  process.exit(0); // Don't fail the install
}
