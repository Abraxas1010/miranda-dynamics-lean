# Reproducibility Guide

## Requirements

- **Lean**: v4.24.0 (specified in `lean-toolchain`)
- **Mathlib**: v4.24.0
- **OS**: Linux, macOS, or Windows with WSL

## Quick Start

```bash
cd RESEARCHER_BUNDLE

# Install Lean (if needed)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Get dependencies
lake update

# Build
lake build --wfail

# End-to-end verification (build + demos + WL cross-check + robustness)
./scripts/verify_miranda.sh

# If Wolfram isn't available locally, skip the WL echo check
./scripts/verify_miranda.sh --no-wolfram
```

## Build Outputs

After successful build:
```
.lake/build/lib/HeytingLean/MirandaDynamics/*.olean  # Compiled files
.lake/build/bin/miranda_*                            # Demo executables
```

## Running Demos

```bash
lake exe miranda_dynamics_demo
lake exe miranda_billiards_demo
lake exe miranda_discrete_demo
```

## Verification Checklist

1. **Zero sorries**:
   ```bash
   grep -r "sorry" HeytingLean/MirandaDynamics/ && echo "FAIL" || echo "PASS"
   ```

2. **Zero admits**:
   ```bash
   grep -r "admit" HeytingLean/MirandaDynamics/ && echo "FAIL" || echo "PASS"
   ```

3. **No axioms** (except Mathlib's):
   ```bash
   grep -r "axiom" HeytingLean/MirandaDynamics/ && echo "CHECK" || echo "PASS"
   ```

4. **Build with warnings as errors**:
   ```bash
   lake build --wfail
   ```

## Troubleshooting

### Mathlib Cache

Speed up builds by downloading precompiled Mathlib:
```bash
lake exe cache get
```

The verification script automatically skips cache fetching when a local Mathlib cache is already present (`.lake/packages/mathlib/.lake/build/lib`).

### Memory Issues

If builds fail with OOM:
```bash
lake build -j1  # Single-threaded build
```

### Version Mismatch

Ensure `lean-toolchain` matches:
```bash
cat lean-toolchain
# Should show: leanprover/lean4:v4.24.0
```

## CI/CD

This repo can be verified with GitHub Actions:

```yaml
# .github/workflows/verify.yml
name: Verify
on: [push, pull_request]
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
        with:
          lake-package-directory: RESEARCHER_BUNDLE
      - run: cd RESEARCHER_BUNDLE && lake build --wfail
      - run: ./RESEARCHER_BUNDLE/scripts/verify_miranda.sh
```

## Contact

For build issues, open an issue on GitHub or contact the maintainers.
