#!/usr/bin/env node
/**
 * Watch for .next directory changes and copy Z3 WASM files
 * 
 * This script runs in the background during development to ensure
 * Z3 WASM files are always available after hot reloads or rebuilds.
 */

const fs = require('fs');
const path = require('path');
const { exec } = require('child_process');

const nextDir = path.join(__dirname, '..', '.next');
const vendorChunksDir = path.join(nextDir, 'server', 'vendor-chunks');

let isWatching = false;
let copyScheduled = false;

function copyZ3Files() {
  if (copyScheduled) return;
  
  copyScheduled = true;
  setTimeout(() => {
    exec('node scripts/copy-z3-wasm.js', (error, stdout, stderr) => {
      if (error) {
        console.error('Error copying Z3 files:', error.message);
      } else {
        console.log(stdout);
      }
      copyScheduled = false;
    });
  }, 500);
}

function startWatching() {
  if (isWatching) return;
  
  try {
    // Watch the .next directory
    fs.watch(nextDir, { recursive: true }, (eventType, filename) => {
      if (filename && filename.includes('vendor-chunks')) {
        console.log('📦 Detected .next build change, copying Z3 files...');
        copyZ3Files();
      }
    });
    
    isWatching = true;
    console.log('👀 Watching .next directory for changes...');
  } catch (error) {
    console.log('⚠️  Could not watch .next directory (will be created on first build)');
  }
}

// Initial copy
copyZ3Files();

// Start watching if .next exists
if (fs.existsSync(nextDir)) {
  startWatching();
} else {
  // Wait for .next to be created
  const interval = setInterval(() => {
    if (fs.existsSync(nextDir)) {
      clearInterval(interval);
      copyZ3Files();
      startWatching();
    }
  }, 1000);
}

// Keep the script running
process.on('SIGINT', () => {
  console.log('\n👋 Stopping Z3 watcher...');
  process.exit(0);
});

