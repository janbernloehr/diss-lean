#!/usr/bin/env bash
# Focused checks with private outputs and a read-only compiled-import overlay.
set -euo pipefail
article_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
reference_root="${DISS_LEAN_REFERENCE:-/home/janbernloehr/Documents/Codex/2026-09-11/test-01-5-2-test-02/outputs/dnls}"
export ELAN_HOME="${ELAN_HOME:-/home/janbernloehr/Documents/Codex/2026-09-11/test-01-5-2-test-02/work/tooling/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="${MATHLIB_CACHE_DIR:-/home/janbernloehr/Documents/Codex/2026-09-11/test-01-5-2-test-02/work/cache/mathlib}"
article_build="$article_root/.lake/build/lib/lean"
article_imports="$article_root/.lake/article-imports"
modules=(NLS/ComplexAnalysis/BanachTaylorBounds
  NLS/ZakharovShabat/ClassicalHorizontalStripBounds
  NLS/ComplexAnalysis/JointSpectralDerivative
  NLS/ComplexAnalysis/ParametricDividedDifference
  NLS/ComplexAnalysis/AnalyticFinitePeriodNormalization
  NLS/ComplexAnalysis/RightHalfPlaneSquareRoot
  NLS/ComplexAnalysis/RationalCircleIntegrationByParts
  NLS/ZakharovShabat/ContinuousPotentialL2Bound
  NLS/ZakharovShabat/SourceDistantCriticalPointsAnalyticNeighborhood
  NLS/KdV/ConstantUpperSpectralBridge
  NLS/KdV/ClassicalSpectralSymmetry
  NLS/KdV/ClassicalDiscriminant
  NLS/KdV/ClassicalLocalPrimitive
  NLS/KdV/ClassicalDiscriminantUniformVariation
  NLS/KdV/ClassicalFreePrimitive
  NLS/KdV/ClassicalHillFlow
  NLS/KdV/ClassicalHillSpectrum
  NLS/KdV/ClassicalSourcePrimitive
  NLS/KdV/ClassicalSpectralEmbedding
  NLS/KdV/ClassicalContourCoverage
  NLS/KdV/ActionHamiltonianMoments
  NLS/KdV/ClassicalContourMoments
  NLS/KdV/ClassicalHighContourMoments
  NLS/KdV/ClassicalBranchPrimitive
  NLS/SequenceSpaces/LocallyBoundedAnalyticSummation
  NLS/KdV/FrequencySeriesBounds
  NLS/KdV/FrequencySeries
  NLS/SequenceSpaces/NonnegativeEnergyDivergence
  NLS/SequenceSpaces/HilbertEnergyDivergence
  NLS/Dynamics/ActionDependentWeightedPhaseFlow
  NLS/Dynamics/FixedTimePhaseObstruction
  NLS/KdV/FrequencyMoments
  NLS/KdV/FreeFrequencyPsi
  NLS/KdV/FreeHighContourPeriods
  NLS/KdV/FreeContourUniformLowerBound
  NLS/KdV/ClassicalUniformRootBounds
  NLS/KdV/ClassicalUniformPrimitiveBounds
  NLS/KdV/ClassicalCriticalPointBranch
  NLS/KdV/ClassicalHighCriticalPoints
  NLS/KdV/HighEnergyContourSeparation
  NLS/KdV/ClassicalUniformCriticalBasis
  NLS/KdV/ClassicalCriticalTailAnalytic
  NLS/KdV/ClassicalUniformCriticalLocalization
  NLS/KdV/ClassicalCriticalNumerator
  NLS/KdV/ClassicalCriticalPeriods
  NLS/KdV/ClassicalFiniteNormalizedDifferentials
  NLS/KdV/ClassicalUniformPeriodEntries
  NLS/KdV/ClassicalPeriodIntegrationByParts
  NLS/KdV/ClassicalUniformPeriodBounds
  NLS/KdV/FrequencyPrimitiveContinuation
  NLS/KdV/FrequencyContourDecomposition
  NLS/Articles/KdVKdV2Frequencies/SignedPhaseFlow
  NLS/Articles/KdVKdV2Frequencies/MassPhaseObstruction
  NLS/Articles/KdVKdV2Frequencies/SmoothKdVIdentities
  NLS/Articles/KdVKdV2Frequencies/SignedMassDivergence
  NLS/Articles/KdVKdV2Frequencies/SignedMassInsertion
  NLS/Articles/KdVKdV2Frequencies/FixedTimeNonextension)
python3 - "$reference_root" "$article_imports" "$article_build" "${modules[@]}" <<'PY'
from pathlib import Path
import sys
reference = Path(sys.argv[1]) / '.lake/build/lib/lean/NLS'
overlay, build = Path(sys.argv[2]), Path(sys.argv[3])
modules = sys.argv[4:]
def fill(source, dest):
    for item in source.iterdir():
        target = dest / item.name
        if target.is_symlink():
            continue
        if target.exists():
            if item.is_dir() and target.is_dir():
                fill(item, target)
        else:
            target.symlink_to(item, target_is_directory=item.is_dir())
def local_directory(path):
    if path == overlay:
        path.mkdir(parents=True, exist_ok=True)
        return
    local_directory(path.parent)
    if path.is_symlink():
        source = path.resolve()
        path.unlink()
        path.mkdir()
        fill(source, path)
    else:
        path.mkdir(exist_ok=True)
for module in modules:
    target = build / (module + '.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.is_symlink() or not target.parent.resolve().is_relative_to(build.resolve()):
        raise SystemExit(f'Expected a private build output: {target}')
    link = overlay / (module + '.olean')
    local_directory(link.parent)
    if link.is_symlink():
        link.unlink()
    elif link.exists():
        raise SystemExit(f'Expected an import symlink: {link}')
    link.symlink_to(target)
fill(reference, overlay / 'NLS')
PY
if [[ "${1:-}" == --prepare-only ]]; then
  exit 0
fi
export LEAN_PATH="$article_imports:$reference_root/.lake/build/lib/lean"
for package in "$reference_root"/.lake/packages/*; do
  if [[ -d "$package/.lake/build/lib/lean" ]]; then
    export LEAN_PATH="$LEAN_PATH:$package/.lake/build/lib/lean"
  fi
done
article_lean="$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1/bin/lean"
"$article_lean" --version
for module in "${modules[@]}"; do
  "$article_lean" -DautoImplicit=false -DwarningAsError=true -R "$article_root" \
    -o "$article_build/$module.olean" "$article_root/$module.lean"
  echo "PASS $module"
done
"$article_lean" -DautoImplicit=false -DwarningAsError=true -R "$article_root" \
  "$article_root/scripts/CheckKdVKdV2FrequencyCandidates.lean"
