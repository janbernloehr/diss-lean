#!/usr/bin/env bash
# Focused direct-Lean checks using read-only canonical compiled dependencies.
set -euo pipefail
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
project_dir="$(cd -- "$script_dir/../../.." && pwd)"
canonical="${CANONICAL_NLS_ROOT:-/home/janbernloehr/Documents/Codex/2026-09-11/test-01-5-2-test-02/outputs/dnls}"
export ELAN_HOME="${ELAN_HOME:-/home/janbernloehr/Documents/Codex/2026-09-11/test-01-5-2-test-02/work/tooling/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="${MATHLIB_CACHE_DIR:-/home/janbernloehr/Documents/Codex/2026-09-11/test-01-5-2-test-02/work/cache/mathlib}"
lean_bin="${LEAN_BIN:-$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1/bin/lean}"
build_root="${MKDV_BUILD_ROOT:-$project_dir/.lake/mkdv-below-l2/lib/lean}"
mkdir -p "$build_root/NLS/Articles/MKdVBelowL2"
# New modules coexist with read-only symlinks to the established namespaces.
for namespace in SequenceSpaces Fourier ComplexAnalysis FunctionalAnalysis ZakharovShabat MKdV Dynamics Poisson; do
  target="$build_root/NLS/$namespace"
  if [[ -L "$target" ]]; then
    rm "$target"
  fi
  mkdir -p "$target"
  if [[ -d "$canonical/.lake/build/lib/lean/NLS/$namespace" ]]; then
    for entry in "$canonical/.lake/build/lib/lean/NLS/$namespace"/*; do
      if [[ ! -e "$target/${entry##*/}" ]]; then
        ln -s "$entry" "$target/${entry##*/}"
      fi
    done
  fi
done
for entry in "$canonical"/.lake/build/lib/lean/NLS/*; do
  name="${entry##*/}"
  if [[ "$name" != Articles && ! -e "$build_root/NLS/$name" ]]; then
    ln -s "$entry" "$build_root/NLS/$name"
  fi
done
export LEAN_PATH="$build_root:$canonical/.lake/build/lib/lean"
for pkg in "$canonical"/.lake/packages/*; do
  if [[ -d "$pkg/.lake/build/lib/lean" ]]; then
    export LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"
  fi
done
cd "$project_dir"
"$lean_bin" --version
modules=(
  ComplexAnalysis/RelativeProductComparison
  ComplexAnalysis/RootPeriodComparison
  ComplexAnalysis/QuarticInversionRemainder
  ComplexAnalysis/QuarticInversionContour
  ZakharovShabat/SourceFullAbelianFourthHamiltonianContour
  ZakharovShabat/SourceFullAbelianFourthContourPoisson
  ZakharovShabat/SourceFullAbelianFourthContourLocal
  ZakharovShabat/SourceAbelianMomentCubicShift
  ZakharovShabat/SourceAbelianMomentFourthContour
  ZakharovShabat/SourceFiniteGapFourthOpenFrequency
  ZakharovShabat/SourceFiniteGapFourthOpenMoments
  ZakharovShabat/SourceFiniteGapFourthOpening
  ZakharovShabat/SourceFiniteGapFourthClosedFrequency
  ZakharovShabat/SourceLemma5_2
  ZakharovShabat/SourceFiniteGapFourthFrequencyExponent
  ZakharovShabat/SourceSingleRootRelativeComparison
  ZakharovShabat/SourcePsiCriticalRootComparison
  ZakharovShabat/SourceCriticalRelativeComparison
  ZakharovShabat/SourcePsiCriticalComparisonDomain
  ZakharovShabat/SourceRootPeriodPerturbation
  Fourier/AbsoluteReciprocalYoungRows
  ZakharovShabat/SourceCriticalRelativeRowBound
  ZakharovShabat/SourceCriticalTailSeparation
  ZakharovShabat/SourcePsiCriticalFilledTail
  ZakharovShabat/SourcePsiCriticalNormalizer
  ZakharovShabat/SourcePsiCriticalPeriodLowerBound
  ZakharovShabat/SourcePsiCriticalRootBound
  SequenceSpaces/ReciprocalBootstrapExponents
  SequenceSpaces/ReciprocalBootstrapStep
  SequenceSpaces/ReciprocalBootstrap
  ZakharovShabat/SourcePsiCriticalInitialOffset
  ZakharovShabat/SourcePsiCriticalReciprocalInequality
  ZakharovShabat/SourceProposition4_1
  ComplexAnalysis/QuadraticCosineWeightedCancellation
  ZakharovShabat/SourceAbelianCriticalWeightedPeriod
  ZakharovShabat/SourceAbelianCriticalCosineCancellation
  ZakharovShabat/SourceAbelianMomentCriticalComparison
  ZakharovShabat/SourceAbelianMomentCriticalBound
  ZakharovShabat/SourcePsiCriticalSummableDifference
  ZakharovShabat/SourcePsiCriticalProductOnePlus
  ZakharovShabat/SourceAbelianMomentOnePlus
  ZakharovShabat/SourceAbelianMomentOnePlusDomain
  ZakharovShabat/SourceLemma5_3
  SequenceSpaces/WeightedReciprocalRows
  SequenceSpaces/WeightedIndexRealization
  ZakharovShabat/SourceAbelianMomentWeightedRows
  FunctionalAnalysis/ComplexRealEquiv
  Dynamics/ComplexBirkhoffCoordinatesExponent
  Dynamics/ConjugatePairEquiv
  Poisson/ComplexCanonicalCoordinates
  ZakharovShabat/SourceRealBallCoreIdentity
  ZakharovShabat/SourceComplexBirkhoffCanonical
  ZakharovShabat/SobolevHierarchySymmetries
  MKdV/HierarchyRestriction
  ZakharovShabat/ClassicalNLSFourthHamiltonian
  ZakharovShabat/ClassicalNLSFourthVariation
  MKdV/ClassicalEnergyVariation
  MKdV/ClassicalFourthFlowRestriction
  Articles/MKdVBelowL2/SmoothRenormalization
  Articles/MKdVBelowL2/TranslationFourier
  Articles/MKdVBelowL2/PhysicalBirkhoff
  Articles/MKdVBelowL2/CompatibleBirkhoffFamily
  Articles/MKdVBelowL2/PhysicalBirkhoffCanonical
  Articles/MKdVBelowL2/HilbertBirkhoffIdentification
  Articles/MKdVBelowL2/RealBirkhoffFamily
  Articles/MKdVBelowL2/Theorem12
  Articles/MKdVBelowL2/ClassicalRenormalizedFourthFlow
  Articles/MKdVBelowL2/FourthMomentSummability
  Articles/MKdVBelowL2/FourthMomentSharpSummability
  Articles/MKdVBelowL2/FourthMomentAnalytic
  Articles/MKdVBelowL2/FourthMomentSequence
  Articles/MKdVBelowL2/FourthMomentActionRemainder
  Articles/MKdVBelowL2/PhysicalFourthFrequencyCandidate
  Articles/MKdVBelowL2/PhysicalFourthFrequencyRemainder
  Articles/MKdVBelowL2/PhysicalFourthFrequencyIdentification
  Articles/MKdVBelowL2/FourthMomentReality
  Articles/MKdVBelowL2/PhysicalFourthFrequencyReality
  ZakharovShabat/PeriodOneSobolevFourthHamiltonian
  ZakharovShabat/PeriodOneSobolevFourthClassical
  ZakharovShabat/SourceFiniteGapHamiltonianReality
  ZakharovShabat/SourceSobolevFourthHamiltonian
  ZakharovShabat/SourceSobolevFourthBirkhoff
  ZakharovShabat/SourceFiniteGapHamiltonianIsospectral
  SequenceSpaces/WeightedRealTruncation
  ZakharovShabat/SourceSobolevFourthActionDependence
  SequenceSpaces/WeightedRealActionReduction
  ZakharovShabat/SourceSobolevActionReduction
  ZakharovShabat/SourceSobolevFourthFrequency
)
for module in "${modules[@]}"; do
  mkdir -p "$build_root/NLS/$(dirname "$module")"
  if [[ -L "$build_root/NLS/$module.olean" ]]; then
    printf 'Refusing to write through canonical import symlink: %s\n' "$module" >&2
    exit 1
  fi
  "$lean_bin" -DautoImplicit=false -DwarningAsError=true -o "$build_root/NLS/$module.olean" "NLS/$module.lean"
  printf '%s: checked\n' "$module"
done
"$lean_bin" -DautoImplicit=false -DwarningAsError=true NLS/Articles/MKdVBelowL2/AxiomAudit.lean
