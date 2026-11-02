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
  NLS/SequenceSpaces/Convolution
  NLS/SequenceSpaces/Reflection
  NLS/SequenceSpaces/Multiplier
  NLS/SequenceSpaces/PositiveOddMultiplier
  NLS/ZakharovShabat/ClassicalHorizontalStripBounds
  NLS/SequenceSpaces/PositiveIndexWeight
  NLS/SequenceSpaces/PuncturedLattice
  NLS/SequenceSpaces/PositiveIndexPowerWeight
  NLS/SequenceSpaces/OperatorBasisExt
  NLS/SequenceSpaces/DiagonalIntertwining
  NLS/SequenceSpaces/BoundedCoordinateDifferentiable
  NLS/SequenceSpaces/CoordinateQuadraticDerivative
  NLS/SequenceSpaces/HolderEmbedding
  NLS/SequenceSpaces/BoundedCoordinateAnalytic
  NLS/ComplexAnalysis/JointSpectralDerivative
  NLS/ComplexAnalysis/AnalyticOperatorInverse
  NLS/SequenceSpaces/ConvolutionDominatedMatrix
  NLS/SequenceSpaces/LocallyBoundedRealization
  NLS/SequenceSpaces/TwoSequenceBound
  NLS/SequenceSpaces/FiniteHeadTailBound
  NLS/SequenceSpaces/AnalyticReciprocalTail
  NLS/SequenceSpaces/ConjugateDuality
  NLS/ComplexAnalysis/BilinearCircleIntegral
  NLS/SequenceSpaces/ConvolutionMatrixAnalytic
  NLS/SequenceSpaces/RankOneDominatedMatrix
  NLS/SequenceSpaces/MixedMajorantMatrix
  NLS/SequenceSpaces/ReciprocalSquareKernel
  NLS/ComplexAnalysis/ParametricDividedDifference
  NLS/ComplexAnalysis/AnalyticImplicitBanachRoot
  NLS/ComplexAnalysis/AnalyticFinitePeriodNormalization
  NLS/ComplexAnalysis/RightHalfPlaneSquareRoot
  NLS/ComplexAnalysis/EntireLimit
  NLS/ComplexAnalysis/LocalAnalyticSquareRoot
  NLS/ComplexAnalysis/SquareProductConvergence
  NLS/ComplexAnalysis/RemovableFactorConvergence
  NLS/ComplexAnalysis/RationalCircleIntegrationByParts
  NLS/ZakharovShabat/ContinuousPotentialL2Bound
  NLS/SequenceSpaces/FiniteModification
  NLS/ZakharovShabat/FreeDerivativeZeroCounts
  NLS/ZakharovShabat/CriticalPointLabeling
  NLS/ZakharovShabat/DiscriminantDerivativeProduct
  NLS/ZakharovShabat/SourceDistantCriticalPointsAnalyticNeighborhood
  NLS/ZakharovShabat/NearFreeCriticalRelabeling
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
  NLS/ComplexAnalysis/AnalyticSquareDescent
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
  NLS/KdV/HighEnergyDiscSeparation
  NLS/KdV/PositiveEnergyResolventKernel
  NLS/KdV/ClassicalCriticalNumerator
  NLS/KdV/ClassicalUniformCriticalBasis
  NLS/KdV/ClassicalCriticalTailAnalytic
  NLS/KdV/ClassicalUniformCriticalLocalization
  NLS/KdV/ClassicalCriticalPeriods
  NLS/KdV/ClassicalFiniteNormalizedDifferentials
  NLS/KdV/ClassicalUniformPeriodEntries
  NLS/KdV/ClassicalPeriodIntegrationByParts
  NLS/KdV/ClassicalUniformPeriodBounds
  NLS/KdV/ClassicalAllContourPeriods
  NLS/KdV/ClassicalAllContourPeriodBounds
  NLS/KdV/ClassicalPeriodOperator
  NLS/KdV/ClassicalPeriodInverse
  NLS/KdV/ClassicalWeightedPeriodOperator
  NLS/KdV/ClassicalTwoWeightedPeriodOperator
  NLS/KdV/ClassicalWeightedPeriodInverse
  NLS/KdV/ClassicalTwoWeightedPeriodInverse
  NLS/KdV/ClassicalNumeratorHilbert
  NLS/KdV/ClassicalHilbertPeriod
  NLS/KdV/ClassicalNormalizedDifferentials
  NLS/KdV/ClassicalWeightedNormalizedCoefficients
  NLS/KdV/ClassicalTwoWeightedNormalizedCoefficients
  NLS/KdV/ClassicalNormalizedResidues
  NLS/KdV/ClassicalCandidateZeros
  NLS/SequenceSpaces/CompactPuncturedKernel
  NLS/KdV/ClassicalCandidateResolvents
  NLS/KdV/ClassicalNormalizedZeroMap
  NLS/KdV/ClassicalNormalizedRootBranches
  NLS/KdV/ClassicalNormalizedZeroIdentity
  NLS/KdV/ClassicalNormalizedZeros
  NLS/KdV/ClassicalSignedCriticalProduct
  NLS/KdV/ClassicalCandidateNumeratorUnits
  NLS/KdV/ClassicalNormalizedZeroFactorization
  NLS/KdV/ClassicalNormalizedZeroDerivative
  NLS/KdV/ClassicalNormalizedSimpleZeros
  NLS/ZakharovShabat/SourceGapInterpolationProduct
  NLS/KdV/ClassicalCandidateRootProducts
  NLS/ComplexAnalysis/CauchyFiniteHoles
  NLS/ComplexAnalysis/OddSquareDescent
  NLS/ZakharovShabat/PairedEnergyProduct
  NLS/ZakharovShabat/SourcePsiRootResolventExterior
  NLS/ZakharovShabat/PairedEnergyResolventExterior
  NLS/ZakharovShabat/SingleSpectralProductRatioExterior
  NLS/ZakharovShabat/PairedEnergyZeros
  NLS/ZakharovShabat/OmittedPairedEnergyProduct
  NLS/KdV/ClassicalCriticalEnergyProduct
  NLS/KdV/ClassicalCriticalBasisProduct
  NLS/KdV/ClassicalCandidateEnergyProducts
  NLS/ComplexAnalysis/FilledSimpleQuotient
  NLS/KdV/ClassicalNormalizedProductQuotient
  NLS/KdV/ClassicalNormalizedResolventExterior
  NLS/KdV/ClassicalNormalizedProductAsymptotics
  NLS/ComplexAnalysis/EntireCircleDecay
  NLS/ZakharovShabat/CentralCircleThresholds
  NLS/KdV/ClassicalNormalizedProductConstant
  NLS/KdV/FrequencyPrimitiveContinuation
  NLS/KdV/FrequencyContourDecomposition
  NLS/Articles/KdVKdV2Frequencies/SignedPhaseFlow
  NLS/Articles/KdVKdV2Frequencies/MassPhaseObstruction
  NLS/Articles/KdVKdV2Frequencies/SmoothKdVIdentities
  NLS/Articles/KdVKdV2Frequencies/SignedMassDivergence
  NLS/Articles/KdVKdV2Frequencies/SignedMassInsertion
  NLS/Articles/KdVKdV2Frequencies/FixedTimeNonextension
  NLS/KdV/ClassicalCoshStripControl
  NLS/KdV/ClassicalHillDiscAsymptotics
  NLS/KdV/ClassicalHillHighTracePhase
  NLS/KdV/ClassicalHillSmallDiscTrace
  NLS/KdV/ClassicalHillSmallGapCoverage
  NLS/ZakharovShabat/ClassicalSolutionInjectivity
  NLS/KdV/ClassicalHillGreen
  NLS/KdV/ClassicalHighGapPairs
  NLS/KdV/ClassicalHillReality
  NLS/KdV/ClassicalHillConjugation
  NLS/ComplexAnalysis/ContinuousSquareRootPath
  NLS/KdV/ClassicalHillPrimitiveSheets
  NLS/KdV/ClassicalHillPrimitiveReflection
  NLS/KdV/ClassicalHillBandNormalization
  NLS/KdV/ClassicalHillHighPrimitiveStrip
  NLS/KdV/ClassicalHillHighEndpointNormalization
  NLS/KdV/ClassicalHillSquaredPrimitiveMatching
  NLS/KdV/ClassicalHillWholeGapSquares
  NLS/KdV/ClassicalHillAnnulusCoverage
  NLS/KdV/ClassicalHillWholeGapQuotients
  NLS/KdV/ClassicalNormalizedMoments
  NLS/KdV/ClassicalHillOddDifferentialMoments
  NLS/KdV/ClassicalHillLowOddDifferentialMoments
  NLS/KdV/ClassicalNormalizedOddMoments
  NLS/ComplexAnalysis/TwoRootQuotientDiscBound
  NLS/ComplexAnalysis/TwoZeroDeflation
  NLS/KdV/ClassicalHillGapQuotients
  NLS/ComplexAnalysis/AnalyticDiscSquareRoot
  NLS/KdV/ClassicalHillCollapsedDifferentialMoments
  NLS/KdV/ClassicalNormalizedCollapsedMoments)
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
