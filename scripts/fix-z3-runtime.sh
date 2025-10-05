#!/bin/bash
#
# Quick fix for Z3 WASM loading issues
# Run this after starting the dev server if you see WASM errors
#

echo "🔧 Fixing Z3 WASM runtime paths..."

# Wait for .next to be created
while [ ! -d ".next/server/vendor-chunks" ]; do
  echo "⏳ Waiting for Next.js to create build directory..."
  sleep 2
done

# Copy Z3 files
node scripts/copy-z3-wasm.js

echo "✅ Z3 WASM files updated!"
echo "🔄 Please refresh your browser or retry the verification."

