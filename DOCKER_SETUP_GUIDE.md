# 🐳 Docker Setup & Integration Guide

## Overview

Guardrails: Atomic uses Docker for **two purposes**:

1. **TLC Model Checker** (Required) - Runs TLA+ verification
2. **Next.js Application** (Optional) - For containerized deployment

This guide focuses on the **TLC Docker setup**, which is essential for the verification pipeline.

---

## 📁 Docker File Structure

```
guardrails-atomic/
├── docker/
│   ├── tlc/
│   │   └── Dockerfile           # TLC model checker image ⭐ (MAIN)
│   ├── Dockerfile               # Next.js app image (optional)
│   └── docker-compose.yml       # Multi-container setup (optional)
```

---

## 🎯 TLC Docker Image (Core Component)

### Purpose

The TLC Docker image encapsulates the TLA+ model checker, allowing:
- ✅ Isolated execution environment
- ✅ Consistent TLC version across machines
- ✅ No Java installation required on host
- ✅ ARM/Apple Silicon support
- ✅ Easy cleanup (no file system pollution)

### Dockerfile Breakdown

**File**: `docker/tlc/Dockerfile`

```dockerfile
FROM eclipse-temurin:17-jre
# Uses Eclipse Temurin (OpenJDK) Java 17
# Works on both x86_64 and ARM64 (Apple Silicon)

WORKDIR /opt

# Install TLA+ Toolbox (tla2tools.jar)
RUN apt-get update && \
    apt-get install -y wget && \
    wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*
# Downloads TLA+ Tools v1.8.0 (latest stable)
# Cleans up apt cache to reduce image size

WORKDIR /workspace
# All TLA+ files will be mounted here

ENTRYPOINT ["java", "-cp", "/opt/tla2tools.jar", "tlc2.TLC"]
# Runs TLC directly when container starts
# Any arguments passed to container go to TLC
```

**Image Details**:
- **Base Image**: eclipse-temurin:17-jre (~180MB)
- **Final Size**: ~250MB (with TLA+ tools)
- **TLC Version**: 2.20 (from tla2tools.jar v1.8.0)
- **Architecture**: Multi-arch (amd64, arm64)

---

## 🔗 Integration with TLC Runner

### How It Works

The TLC runner (`lib/verification/tlc-runner.ts`) orchestrates Docker execution:

```typescript
// High-level flow:
1. Check if Docker image exists
2. Build image if needed (first run only)
3. Create temporary directory for TLA+ files
4. Write .tla and .cfg files
5. Run Docker container with volume mount
6. Parse TLC output
7. Extract counterexamples if violations found
8. Clean up temporary files
9. Return structured results
```

### Step-by-Step Integration

#### 1. **Ensure Docker Image Exists**

```typescript
async function ensureDockerImage(): Promise<void> {
  // Check if image exists
  const { stdout } = await execAsync('docker images -q guardrails-tlc');
  
  if (!stdout.trim()) {
    // Image doesn't exist, build it
    logger.info('TLC Docker image not found, building...');
    
    const dockerfilePath = path.join(process.cwd(), 'docker', 'tlc');
    await execAsync(`docker build -t guardrails-tlc "${dockerfilePath}"`, {
      timeout: 120000, // 2 minutes
    });
    
    logger.info('TLC Docker image built successfully');
  }
}
```

**What happens**:
- On first run, automatically builds the image
- Subsequent runs skip building (image cached)
- Takes ~1-2 minutes on first run

#### 2. **Create Temporary Workspace**

```typescript
// Create unique temporary directory
const timestamp = Date.now();
const randomId = Math.random().toString(36).substring(7);
const workDir = path.join(os.tmpdir(), `tla-${timestamp}-${randomId}`);

await mkdir(workDir, { recursive: true });
```

**Why unique directories**:
- Allows parallel TLC executions
- Prevents file conflicts
- Easy cleanup after verification

**Example**: `/tmp/tla-1696531200000-abc123/`

#### 3. **Write TLA+ Files**

```typescript
// Extract module name from spec
const moduleMatch = tlaSpec.match(/----\s*MODULE\s+(\w+)\s*----/);
const moduleName = moduleMatch ? moduleMatch[1] : 'Spec';

// Write files
const specPath = path.join(workDir, `${moduleName}.tla`);
const cfgPath = path.join(workDir, `${moduleName}.cfg`);

await writeFile(specPath, tlaSpec, 'utf-8');
await writeFile(cfgPath, configFile, 'utf-8');
```

**TLA+ requires**:
- Module name in spec matches filename
- Config file has same base name
- Example: `transfer_atomic.tla` + `transfer_atomic.cfg`

#### 4. **Run Docker Container**

```typescript
const dockerCommand = [
  'docker run --rm',                      // Remove container after run
  `-v "${workDir}:/workspace"`,           // Mount temp dir
  'guardrails-tlc',                       // Image name
  `-config ${moduleName}.cfg`,            // TLC config flag
  `${moduleName}.tla`,                    // TLA+ spec file
].join(' ');

// Example command:
// docker run --rm -v "/tmp/tla-1696531200000-abc123:/workspace" \
//   guardrails-tlc -config transfer_atomic.cfg transfer_atomic.tla

const { stdout, stderr } = await execAsync(dockerCommand, {
  timeout: 60000,        // 60 second timeout
  maxBuffer: 10485760,   // 10MB buffer
});
```

**Docker flags explained**:
- `--rm` - Delete container after execution (no cleanup needed)
- `-v` - Mount host directory to container's `/workspace`
- No `-d` - Run synchronously (wait for completion)
- No ports - TLC doesn't need network access

#### 5. **Parse TLC Output**

```typescript
const output = stdout + '\n' + stderr;

// Check success/failure
const success = isSuccess(output);

// Extract metrics
const { statesExplored, distinctStates } = parseStateMetrics(output);

// Extract invariants checked
const invariantsChecked = extractInvariants(output);

// If violations, parse counterexample
let counterExample = null;
let violations: InvariantViolation[] = [];

if (!success) {
  violations = parseViolations(output);
  counterExample = parseCounterExample(output);
}
```

#### 6. **Clean Up**

```typescript
// Remove temporary directory
if (workDir) {
  await rm(workDir, { recursive: true, force: true });
}
```

---

## 🚀 Setup Instructions

### Prerequisites

1. **Docker Desktop** (Mac/Windows) or **Docker Engine** (Linux)
   ```bash
   # Check if Docker is installed
   docker --version
   # Should show: Docker version 24.x.x or higher
   
   # Check if Docker is running
   docker ps
   # Should show: empty list or running containers
   ```

2. **Node.js 20+** (for running the project)
   ```bash
   node --version
   # Should show: v20.x.x or higher
   ```

### Step 1: Clone & Install

```bash
# Clone the repository
git clone <your-repo-url>
cd guardrails-atomic

# Install dependencies
pnpm install
```

### Step 2: Build TLC Docker Image

**Option A: Manual Build** (Recommended)

```bash
# Navigate to TLC Dockerfile directory
cd docker/tlc

# Build the image
docker build -t guardrails-tlc .

# Verify it was created
docker images | grep guardrails-tlc
```

**Expected output**:
```
guardrails-tlc   latest   abc123def456   2 minutes ago   248MB
```

**Option B: Automatic Build** (On First Run)

The TLC runner automatically builds the image on first use:

```bash
# Just run the test - image will be built automatically
cd ../../
node --loader tsx --no-warnings scripts/test-tla-generation.ts
```

**You'll see**:
```
TLC Docker image not found, building...
[... docker build output ...]
TLC Docker image built successfully
```

### Step 3: Verify Installation

Test that TLC works in Docker:

```bash
# Create a simple test spec
mkdir -p /tmp/tla-test
cat > /tmp/tla-test/Test.tla << 'EOF'
---- MODULE Test ----
EXTENDS Integers

VARIABLE x

Init == x = 0
Next == x' = x + 1
TypeOK == x >= 0

====
EOF

cat > /tmp/tla-test/Test.cfg << 'EOF'
INIT Init
NEXT Next
INVARIANT TypeOK
EOF

# Run TLC
docker run --rm -v /tmp/tla-test:/workspace guardrails-tlc \
  -config Test.cfg Test.tla
```

**Expected output**:
```
TLC2 Version 2.20 of Day Month 20?? (rev: 4c54d98)
...
Model checking completed. No error has been found.
...
Finished in 00s at (2025-10-05 ...)
```

**If you see this**, Docker + TLC is working! ✅

---

## 🧪 Testing the Integration

### Test 1: Run the Test Script

```bash
cd /Users/smyansengupta/guardrails-atomic
node --loader tsx --no-warnings scripts/test-tla-generation.ts
```

**Expected output**:
```
=== TLA+ Generation Test ===

1. Loading transfer.yaml...
✓ Loaded spec: transfer_atomic

2. Generating TLA+ module...
✓ Generated TLA+ module (1691 chars)

3. Generating TLC config...
✓ Generated config file (133 chars)

4. Written files to tla-output/

5. Running TLC model checker...
✅ TLC PASSED!
   States explored: 7
   Duration: 944ms
```

### Test 2: Manual Docker Run

```bash
# Use the generated files from test script
cd tla-output

# Run TLC manually
docker run --rm -v $(pwd):/workspace guardrails-tlc \
  -config transfer_atomic.cfg transfer_atomic.tla
```

### Test 3: Via Web UI

```bash
# Start dev server
pnpm dev

# Open browser
open http://localhost:3000/verify

# Load "Transfer" example → Click "Verify with Formal Proof"
# Should see TLC running and verification completing
```

---

## 🔍 How Docker Execution Works (Visual)

```
┌─────────────────────────────────────────────────────────────┐
│ Host Machine (Your Computer)                                │
│                                                              │
│  ┌──────────────────────────────────────────┐              │
│  │ Node.js Process (tlc-runner.ts)          │              │
│  │                                           │              │
│  │  1. Create /tmp/tla-1234/                │              │
│  │  2. Write transfer_atomic.tla            │              │
│  │  3. Write transfer_atomic.cfg            │              │
│  │                                           │              │
│  │  4. Run docker command ─────────────────────────┐       │
│  └──────────────────────────────────────────┘      │       │
│                                                     │       │
│  ┌──────────────────────────────────────────┐      │       │
│  │ /tmp/tla-1234/ (Host Directory)          │      │       │
│  │  ├── transfer_atomic.tla                 │◄─────┼─┐     │
│  │  └── transfer_atomic.cfg                 │      │ │     │
│  └──────────────────────────────────────────┘      │ │     │
│                                                     ▼ │     │
│  ┌─────────────────────────────────────────────────┐ │     │
│  │ Docker Container (guardrails-tlc)               │ │     │
│  │                                                  │ │     │
│  │  ┌────────────────────────────────────────┐    │ │     │
│  │  │ /workspace/ (Mounted from host)        │◄───┼─┘     │
│  │  │  ├── transfer_atomic.tla               │    │       │
│  │  │  └── transfer_atomic.cfg               │    │       │
│  │  └────────────────────────────────────────┘    │       │
│  │                                                  │       │
│  │  ┌────────────────────────────────────────┐    │       │
│  │  │ TLC Execution                          │    │       │
│  │  │  java -cp tla2tools.jar tlc2.TLC       │    │       │
│  │  │    -config transfer_atomic.cfg          │    │       │
│  │  │    transfer_atomic.tla                  │    │       │
│  │  │                                          │    │       │
│  │  │  ✓ Parse TLA+ files                    │    │       │
│  │  │  ✓ Check invariants                    │    │       │
│  │  │  ✓ Explore state space                 │    │       │
│  │  │  ✓ Generate output                     │    │       │
│  │  └────────────────────────────────────────┘    │       │
│  │                                                  │       │
│  │  Output (stdout/stderr) ──────────────────────────┐     │
│  └─────────────────────────────────────────────────┘ │     │
│                                                       │     │
│  ┌──────────────────────────────────────────┐        │     │
│  │ Node.js Process                           │◄───────┘     │
│  │                                           │              │
│  │  5. Parse TLC output                     │              │
│  │  6. Extract results                       │              │
│  │  7. Clean up /tmp/tla-1234/              │              │
│  │  8. Return TLCResult                      │              │
│  └──────────────────────────────────────────┘              │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

## 🛠️ Troubleshooting

### Issue 1: Docker Not Running

**Error**: `Cannot connect to the Docker daemon`

**Solution**:
```bash
# Mac/Windows: Start Docker Desktop
open -a Docker

# Linux: Start Docker service
sudo systemctl start docker

# Verify
docker ps
```

### Issue 2: Image Build Fails

**Error**: `failed to solve: ... no such file or directory`

**Solution**:
```bash
# Ensure you're in the correct directory
cd /Users/smyansengupta/guardrails-atomic/docker/tlc

# Check Dockerfile exists
ls -la Dockerfile

# Try building with more verbose output
docker build -t guardrails-tlc --progress=plain .
```

### Issue 3: Permission Denied (Linux)

**Error**: `Permission denied while trying to connect to the Docker daemon`

**Solution**:
```bash
# Add your user to docker group
sudo usermod -aG docker $USER

# Log out and back in, or run:
newgrp docker

# Test
docker ps
```

### Issue 4: TLC Timeout

**Error**: `Command failed with ETIMEDOUT`

**Solution**:
```bash
# Increase timeout in tlc-runner.ts (already set to 60s)
# Or check if Docker is slow:
docker run --rm alpine echo "test"

# If slow, restart Docker:
# Mac/Windows: Quit Docker Desktop and restart
# Linux: sudo systemctl restart docker
```

### Issue 5: Volume Mount Fails (Windows)

**Error**: `invalid mount config: ... not an absolute Windows path`

**Solution**:
```bash
# Use WSL2 (recommended) or adjust path format
# In WSL2, paths work normally: /tmp/tla-1234

# In Windows CMD/PowerShell, might need:
# C:\Users\...\AppData\Local\Temp\tla-1234
```

---

## 📊 Docker Performance

### Build Time
- **First build**: 1-2 minutes
- **Rebuilds**: 30 seconds (cached layers)
- **Image size**: ~250MB

### Runtime Performance
- **Container startup**: <1 second
- **TLC execution**: 0.5-5 seconds (simple specs)
- **Cleanup**: <100ms
- **Total overhead**: ~1-2 seconds per verification

### Optimization Tips

1. **Pre-build image** before demos/production:
   ```bash
   docker build -t guardrails-tlc docker/tlc/
   ```

2. **Keep Docker running** to avoid startup delays

3. **Use Docker Desktop settings** to allocate more resources:
   - Resources → 4GB RAM minimum
   - 2 CPU cores minimum

---

## 🚀 Production Deployment

### Option 1: Pre-built Image

```bash
# Build on CI/CD
docker build -t myregistry/guardrails-tlc:latest docker/tlc/

# Push to registry
docker push myregistry/guardrails-tlc:latest

# On production server
docker pull myregistry/guardrails-tlc:latest
```

### Option 2: Docker Compose

```bash
# Use the included docker-compose.yml
cd docker
docker-compose up -d

# The app will automatically use the TLC service
```

### Option 3: Kubernetes

```yaml
# k8s/tlc-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: guardrails-tlc
spec:
  template:
    spec:
      containers:
      - name: app
        image: yourregistry/guardrails-atomic:latest
        volumeMounts:
        - name: docker-socket
          mountPath: /var/run/docker.sock
      volumes:
      - name: docker-socket
        hostPath:
          path: /var/run/docker.sock
```

---

## 📝 Summary

### What Docker Does

✅ **Runs TLC model checker** in isolated container  
✅ **Mounts temporary directory** with TLA+ files  
✅ **Executes verification** and returns results  
✅ **Cleans up automatically** (no leftover containers)  

### Key Files

- `docker/tlc/Dockerfile` - TLC image definition
- `lib/verification/tlc-runner.ts` - Docker integration
- `docker-compose.yml` - Optional multi-container setup

### Integration Flow

1. Node.js creates temp directory
2. Writes TLA+ files
3. Runs Docker container with volume mount
4. TLC verifies in container
5. Output parsed by Node.js
6. Temp directory cleaned up

### Setup Checklist

- [x] Docker installed and running
- [x] TLC image built (`guardrails-tlc`)
- [x] Test script passes
- [x] Manual docker run works
- [x] Web UI verification works

---

**Docker setup complete!** 🎉

Run `docker images | grep guardrails-tlc` to verify your image is ready.

---

*Last Updated*: October 5, 2025  
*Docker Version Tested*: 24.0.6  
*TLC Version*: 2.20 (tla2tools v1.8.0)

