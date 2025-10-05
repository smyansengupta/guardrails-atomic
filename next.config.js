/** @type {import('next').NextConfig} */
const path = require('path');

const nextConfig = {
  output: 'standalone',
  
  // Configure webpack to handle WASM files (needed for z3-solver)
  webpack: (config, { isServer }) => {
    if (isServer) {
      // Enable async WebAssembly
      config.experiments = {
        ...config.experiments,
        asyncWebAssembly: true,
        layers: true,
      };

      // Add rule for .wasm files
      config.module.rules.push({
        test: /\.wasm$/,
        type: 'webassembly/async',
      });

      // Keep z3-solver external but ensure its WASM files are accessible
      // WASM files are copied via the predev/prebuild/postinstall scripts

      // Ensure z3-solver can resolve its WASM file
      config.resolve.alias = {
        ...config.resolve.alias,
        'z3-solver': path.resolve(__dirname, 'node_modules/z3-solver'),
      };
    }

    return config;
  },
}

module.exports = nextConfig
