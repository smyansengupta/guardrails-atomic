# TODO: Z3 WASM Integration

## Current Issue

Z3 WASM files need to be available in multiple locations for Next.js to work properly:
- `public/z3/` - for static file serving
- `.next/server/chunks/` - where Next.js looks during server-side execution
- `.next/server/vendor-chunks/` - alternative location

**Current workaround**: Watch script that copies WASM files when .next directory changes.

**Problem with current solution**:
- Hacky and inelegant
- Requires background process during development
- Files get copied on every rebuild
- Not a sustainable long-term solution

---

## Potential Better Solutions to Explore

### 1. Configure Next.js Webpack for WASM (Already Attempted)
**Status**: Partially implemented in `next.config.ts`

Current config:
```typescript
webpack: (config, { isServer }) => {
  if (isServer) {
    config.experiments = {
      asyncWebAssembly: true,
      layers: true,
    };

    config.module.rules.push({
      test: /\.wasm$/,
      type: 'webassembly/async',
    });

    config.resolve.alias = {
      'z3-solver': path.resolve(process.cwd(), 'node_modules/z3-solver'),
    };
  }

  return config;
}
```

**Next Steps**:
- Research how to properly configure WASM asset loading in Next.js 15
- Look into `output: 'standalone'` configuration
- Test different webpack loader configurations
- Check if we need to use `webpack.NormalModuleReplacementPlugin`

### 2. Custom Z3 Initialization with Path Configuration
**Status**: Not attempted

**Idea**: Modify how we initialize Z3 to explicitly provide WASM path.

Investigate:
- Can we pass custom path to `z3-solver`'s `init()` function?
- Does z3-solver support configuration for WASM location?
- Can we use environment variables to specify WASM path?

**Example pseudocode**:
```typescript
import { init } from 'z3-solver';

const { Context } = await init({
  wasmPath: path.join(process.cwd(), 'public/z3/z3-built.wasm')
});
```

### 3. Use Next.js Static File Serving
**Status**: Partially working (public/z3/ exists)

**Issue**: Z3 doesn't know to look in `public/` directory during server-side execution.

**Investigation needed**:
- Can we set z3-solver's internal path resolution?
- Is there a way to tell Next.js to expose public files to server runtime?
- Can we use `publicRuntimeConfig` in next.config.ts?

### 4. Alternative Z3 Bindings
**Status**: Not explored

**Options**:
- Pure JavaScript Z3 implementation (if exists)
- Different npm package with better Next.js compatibility
- Server-side Z3 binary (via child_process) instead of WASM
- Hosted Z3 service (API-based)

**Trade-offs**:
- Performance
- Installation complexity
- Cross-platform compatibility

### 5. Custom Next.js Plugin for WASM
**Status**: Not attempted

**Idea**: Create a Next.js plugin specifically for handling WASM files.

**Resources**:
- Next.js plugin documentation
- Examples of WASM plugins for Next.js
- Community solutions for similar problems

### 6. Copy WASM to Output Directory Post-Build
**Status**: Not attempted

**Idea**: Hook into Next.js build lifecycle to copy WASM files after build completes.

**Implementation**:
- Use Next.js `experimental.outputFileTracingExcludes` or `outputFileTracingIncludes`
- Post-build script that ensures WASM is in correct location
- Integrate with deployment process

### 7. Monkeypatch z3-solver's File Resolution
**Status**: Not attempted (most hacky, last resort)

**Idea**: Override z3-solver's internal file resolution to point to correct paths.

```typescript
// Pseudocode
const originalRequire = Module.prototype.require;
Module.prototype.require = function(id) {
  if (id.includes('z3-built.wasm')) {
    return originalRequire.call(this, path.join(process.cwd(), 'public/z3/z3-built.wasm'));
  }
  return originalRequire.call(this, id);
};
```

---

## Research Tasks

- [ ] Read z3-solver source code to understand how it resolves WASM paths
- [ ] Check z3-solver GitHub issues for Next.js integration problems
- [ ] Research other Next.js + WASM integration examples
- [ ] Test different Next.js webpack configurations
- [ ] Investigate if z3-solver has initialization options we're missing
- [ ] Look into Next.js 15 specific WASM handling changes

---

## Success Criteria

An ideal solution should:
1. ✅ Work reliably in both development and production
2. ✅ Not require background processes or watchers
3. ✅ Be maintainable and understandable
4. ✅ Follow Next.js best practices
5. ✅ Work with Next.js hot reload without manual copying
6. ✅ Be documented for future developers

---

## Timeline

- **Short-term**: Current watcher solution works but is inelegant
- **Medium-term** (2-3 days): Research and test solutions 1-3
- **Long-term** (1-2 weeks): Implement proper solution and document

---

*Created: 2025-10-08*
*Last Updated: 2025-10-08*
