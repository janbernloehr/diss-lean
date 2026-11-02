#!/usr/bin/env bash
# Standalone focused checks; canonical compiled imports are only read.
set -euo pipefail
repo="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
: "${ELAN_HOME:?Set ELAN_HOME to the pinned Lean 4.33.1 elan directory}"
export PATH="$ELAN_HOME/bin:$PATH"
: "${NLS_REFERENCE_CHECKOUT:?Set NLS_REFERENCE_CHECKOUT to the read-only compiled reference checkout}"
reference="$(cd -- "$NLS_REFERENCE_CHECKOUT" && pwd)"
build="${KDVC_BUILD_DIR:-$repo/.lake/article-checks/kdv-convexity}"
build="$(realpath -m -- "$build")"
if [[ "$build" == "$reference/.lake" || "$build" == "$reference/.lake/"* ]]; then
  echo 'Refusing to write article build output inside the reference cache.' >&2
  exit 1
fi
lean_bin="$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1/bin/lean"
[[ -x "$lean_bin" ]]
if [[ -L "$build/lib/NLS/KdV" ]]; then
  echo "Refusing shared-library output through a linked KdV import directory." >&2
  exit 1
fi
mkdir -p -- "$build/lib/NLS/KdV" "$build/lib/NLS/Articles/KdVConvexity" "$build/logs"
# This shared namespace has a new bounded physical-class inclusion. Replace
# only its private import-directory link, then link reference files as imports.
# Compilation targets below are real files; the reference cache is never written.
if [[ -L "$build/lib/NLS/ZakharovShabat" ]]; then
  unlink -- "$build/lib/NLS/ZakharovShabat"
fi
mkdir -p -- "$build/lib/NLS/ZakharovShabat"
for entry in "$reference/.lake/build/lib/lean/NLS/ZakharovShabat/"*; do
  name="${entry##*/}"
  if [[ ! -e "$build/lib/NLS/ZakharovShabat/$name" ]]; then
    ln -s -- "$entry" "$build/lib/NLS/ZakharovShabat/$name"
  fi
done
# Only specific Lean output paths below are writable build targets. Generic
# namespace links are imports; this directory must never be used by lake build.
for entry in "$reference/.lake/build/lib/lean/NLS/"*; do
  name="$(basename -- "$entry")"
  if [[ "$name" != Articles && ! -e "$build/lib/NLS/$name" ]]; then
    ln -s -- "$entry" "$build/lib/NLS/$name"
  fi
done
import_paths=("$build/lib" "$reference/.lake/build/lib/lean")
for dependency in "$reference"/.lake/packages/*/.lake/build/lib/lean; do
  [[ -d "$dependency" ]] && import_paths+=("$dependency")
done
export LEAN_PATH
LEAN_PATH="$(IFS=:; echo "${import_paths[*]}")"
cd -- "$repo"
for module in ZakharovShabat/ContinuousPotentialL2Bound ZakharovShabat/ClassicalSolutionInjectivity KdV/RiccatiEnergy KdV/ConstantUpperSpectralBridge KdV/ClassicalSpectralSymmetry KdV/ClassicalDiscriminant KdV/ClassicalLocalPrimitive KdV/ClassicalFreePrimitive KdV/ClassicalHillFlow KdV/ClassicalHillSpectrum KdV/ClassicalHillGreen KdV/ClassicalSourcePrimitive KdV/ClassicalSpectralEmbedding KdV/ClassicalContourCoverage KdV/ClassicalHighGapPairs KdV/ClassicalHillReality KdV/ClassicalHillConjugation KdV/ClassicalHillPrimitiveSheets KdV/ClassicalHillPrimitiveReflection KdV/ClassicalHillBandNormalization KdV/ClassicalHillDiscAsymptotics KdV/ClassicalHillHighTracePhase KdV/ClassicalHillHighPrimitiveStrip KdV/ClassicalHillHighEndpointNormalization KdV/ClassicalBranchPrimitive KdV/ClassicalTraceAsymptotics KdV/ActionHamiltonianMoments KdV/ClassicalContourMoments KdV/ClassicalHighContourMoments KdV/ClassicalHillMomentReality KdV/ClassicalHighGapFamilies KdV/ActionHamiltonianTrace KdV/ActionHamiltonianFiniteGap Articles/KdVConvexity/LocalConsequences Articles/KdVConvexity/AnalyticSeries Articles/KdVConvexity/GlobalExtension Articles/KdVConvexity/TailExtension Articles/KdVConvexity/ActionEmbedding Articles/KdVConvexity/BaseContourSeries; do
  log_name="${module//\//.}"
  if [[ -L "$build/lib/NLS/$module.olean" ]]; then
    unlink -- "$build/lib/NLS/$module.olean"
  fi
  if ! "$lean_bin" -R "$repo" -DwarningAsError=true \
      -o "$build/lib/NLS/$module.olean" \
      "$repo/NLS/$module.lean" > "$build/logs/$log_name.log" 2>&1; then
    cat -- "$build/logs/$log_name.log"
    exit 1
  fi
  echo "Checked $module"
done
for check in PositiveIndexExample CheckAxioms; do
  if ! "$lean_bin" -DwarningAsError=true \
      "$repo/coverage/articles/kdv-convexity/$check.lean" > "$build/logs/$check.log" 2>&1; then
    cat -- "$build/logs/$check.log"
    exit 1
  fi
  cat -- "$build/logs/$check.log"
  echo "Checked $check"
done
