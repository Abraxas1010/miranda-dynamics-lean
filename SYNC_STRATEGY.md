# Sync Strategy: miranda-dynamics-lean ↔ heyting-surreal

This document describes how to synchronize development between the standalone
Miranda Dynamics PaperPack and the main HeytingLean repository.

## Overview

The Miranda Dynamics formalization lives in two places:
1. **Standalone repo** (`miranda-dynamics-lean`): For public release, researcher verification
2. **Main repo** (`heyting-surreal`, branch `quantum_extended`): For cross-domain integration

## Directory Mapping

| Standalone | Main Repo |
|------------|-----------|
| `RESEARCHER_BUNDLE/HeytingLean/MirandaDynamics/` | `lean/HeytingLean/MirandaDynamics/` |
| `RESEARCHER_BUNDLE/HeytingLean/Tests/MirandaDynamics/` | `lean/HeytingLean/Tests/MirandaDynamics/` |
| `WIP/miranda_full_completion_extension/` | `WIP/miranda_full_completion_extension/` |

## Sync Workflows

### 1. Standalone → Main (Upstream)

When significant progress is made in the standalone repo:

```bash
# In main repo (heyting-surreal)
cd /path/to/heyting-surreal

# Add standalone as remote (one-time)
git remote add miranda-standalone ../miranda-dynamics-lean

# Fetch and merge MirandaDynamics changes
git fetch miranda-standalone main
git checkout quantum_extended

# Cherry-pick specific commits or merge
git cherry-pick <commit-hash>
# OR for batch updates:
git checkout miranda-standalone/main -- RESEARCHER_BUNDLE/HeytingLean/MirandaDynamics/
cp -r RESEARCHER_BUNDLE/HeytingLean/MirandaDynamics/* lean/HeytingLean/MirandaDynamics/
rm -rf RESEARCHER_BUNDLE/
git add lean/HeytingLean/MirandaDynamics/
git commit -m "sync: Import Miranda updates from standalone repo"
```

### 2. Main → Standalone (Downstream)

When HeytingLean infrastructure changes affect Miranda:

```bash
# In standalone repo
cd /path/to/miranda-dynamics-lean

# Add main as remote (one-time)
git remote add heyting ../heyting-surreal

# Fetch quantum_extended branch
git fetch heyting quantum_extended

# Extract updated MirandaDynamics
git checkout heyting/quantum_extended -- lean/HeytingLean/MirandaDynamics/
mv lean/HeytingLean/MirandaDynamics/* RESEARCHER_BUNDLE/HeytingLean/MirandaDynamics/
rm -rf lean/

# Handle bridge file updates if needed
# (Bridges/Flow.lean, Formal/Nucleus/FixedPoints.lean are standalone versions)

git add RESEARCHER_BUNDLE/
git commit -m "sync: Import updates from HeytingLean quantum_extended"
```

## Bridge Files (Special Handling)

The standalone repo has self-contained versions of these bridge files:

| Standalone | Main Repo Equivalent |
|------------|---------------------|
| `HeytingLean/Bridges/Flow.lean` | `HeytingLean/Bridges/Flow.lean` (full version) |
| `HeytingLean/Formal/Nucleus/FixedPoints.lean` | Same |
| `HeytingLean/MirandaDynamics/Reach.lean` | Uses `ClosingTheLoop.Semantics.RelationalRealizability` |

When syncing, ensure the standalone bridge files remain self-contained.

## Recommended Workflow

1. **Primary development**: Do in standalone repo for clean history
2. **Integration testing**: Test in main repo to ensure cross-domain compatibility
3. **Sync frequency**: After each major feature or proof completion
4. **Version tags**: Tag both repos when syncing major milestones

## Automated Sync (Optional)

A GitHub Action can be set up to:
1. Detect changes in `lean/HeytingLean/MirandaDynamics/` on `quantum_extended`
2. Open a PR in the standalone repo with the changes
3. Require manual review before merge

## Conflict Resolution

If both repos modify the same file:
1. Main repo takes precedence for:
   - Import paths
   - Mathlib version updates
   - Cross-domain integration code
2. Standalone repo takes precedence for:
   - New Miranda-specific theorems
   - Documentation
   - WIP research notes

## Contact

For sync issues, contact the HeytingLean maintainers or open an issue in either repo.
