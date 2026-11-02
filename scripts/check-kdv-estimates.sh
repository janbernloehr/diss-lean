#!/usr/bin/env bash
# Focused checks using immutable compiled dependencies from a pinned reference.
# Set ELAN_HOME/PATH to the repository's Lean 4.33.1 installation first.
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
reference="${DISS_LEAN_REFERENCE_CHECKOUT:?Set DISS_LEAN_REFERENCE_CHECKOUT to the pinned, prebuilt reference checkout}"
build_root="$project_dir/.lake/build/lib/lean"
# Replace a directory symlink by a private directory of read-only imports
# before compiling a new shared module into that namespace.
ensure_private_dir() {
  local target="$build_root/$1"
  if [[ -L "$target" ]]; then
    local backing
    backing="$(readlink -f -- "$target")"
    rm -- "$target"
    mkdir -p "$target"
    for imported_entry in "$backing"/*; do
      ln -s "$imported_entry" "$target/${imported_entry##*/}"
    done
  else
    mkdir -p "$target"
  fi
}
ensure_private_dir NLS/KdV
ensure_private_dir NLS/Articles/KdVEstimates
ensure_private_dir NLS/FunctionalAnalysis
ensure_private_dir NLS/SequenceSpaces
ensure_private_dir NLS/ComplexAnalysis
ensure_private_dir NLS/Fourier
for imported_entry in "$reference"/.lake/build/lib/lean/NLS/*; do
  target="$build_root/NLS/${imported_entry##*/}"
  if [[ ! -e "$target" && ! -L "$target" ]]; then
    ln -s "$imported_entry" "$target"
  fi
done
export LEAN_PATH="$build_root:$reference/.lake/build/lib/lean"
for package_lib in "$reference"/.lake/packages/*/.lake/build/lib/lean; do
  export LEAN_PATH="$LEAN_PATH:$package_lib"
done
cd "$project_dir"
lean --version
modules=(NLS/ComplexAnalysis/EntireEvenSquareDescent NLS/FunctionalAnalysis/TwoDimensionalDeterminant NLS/FunctionalAnalysis/AbsoluteContinuityTranslation NLS/FunctionalAnalysis/LinearVolterraLinearity NLS/SequenceSpaces/WeightedInsertion NLS/SequenceSpaces/PositiveFourierTail NLS/SequenceSpaces/ReciprocalSquareTail NLS/KdV/FreeHill NLS/KdV/HillComplement NLS/KdV/HillReduction NLS/KdV/HillSobolev NLS/KdV/HillPhysical NLS/KdV/HillAnalytic NLS/KdV/HillLocalization NLS/KdV/HillZeroCount NLS/KdV/HillWeightedCoefficients NLS/KdV/HillBilinearSymmetry NLS/KdV/HillSpectralLipschitz NLS/KdV/HillRootSeparation NLS/KdV/HillPeriodOnePotential NLS/KdV/HillGapTail NLS/KdV/ConstantUpperSpectralBridge NLS/KdV/ClassicalSpectralSymmetry NLS/KdV/ClassicalDiscriminant NLS/KdV/ClassicalHillFlow NLS/KdV/HillClassicalIdentification NLS/KdV/ClassicalHillMultipliers NLS/KdV/HillFullPeriod NLS/KdV/HillDiscriminantNecessity NLS/KdV/HillFirstOrderReduction NLS/KdV/HillL2SpectralCriterion NLS/KdV/HillDiscriminantComparison NLS/KdV/HillL2EnergyDiscriminant NLS/KdV/HillWeightIndependence NLS/KdV/HillPhysicalGapBounds NLS/Articles/KdVEstimates/EstimateAdapter)
modules+=(NLS/ComplexAnalysis/ZeroCountHomotopy NLS/ComplexAnalysis/TwoZeroOrderComparison NLS/KdV/ClassicalLocalPrimitive NLS/KdV/ClassicalFreePrimitive NLS/KdV/HillRealSpectrum NLS/KdV/HillCharacteristicZeros NLS/KdV/HillRealGapPairs)
modules+=(NLS/KdV/HillWideLocalization)
modules+=(NLS/ComplexAnalysis/RealDiameterDisc NLS/SequenceSpaces/OrderedOneSidedEnumeration NLS/KdV/HillFreeSpectrum NLS/KdV/HillCentralCounting NLS/KdV/HillCentralRoots NLS/KdV/HillGlobalRealLabels)
modules+=(NLS/KdV/HillRealLabelingUniqueness NLS/KdV/HillCanonicalRealLabels NLS/KdV/HillCanonicalGapBounds)
modules+=(NLS/SequenceSpaces/OrderedFiniteContinuity NLS/KdV/HillCumulativeCounts NLS/KdV/HillLabelContinuity NLS/KdV/HillCanonicalFreeLabels NLS/KdV/HillRealTraceParity)
modules+=(NLS/ComplexAnalysis/TracePrimitiveContinuation NLS/KdV/HillL2SourcePrimitive NLS/ComplexAnalysis/TracePrimitiveMoments NLS/KdV/HillL2HighContourMoments NLS/KdV/HillL2ContourDeformation NLS/Fourier/ContinuousConjugation NLS/KdV/ClassicalHillConjugation NLS/KdV/HillL2Conjugation NLS/ComplexAnalysis/TracePrimitiveReflection NLS/KdV/HillL2PrimitiveReflection)
modules+=(NLS/KdV/HillRealBands)
modules+=(NLS/ComplexAnalysis/RealSimpleZeroSigns NLS/KdV/HillRealGapSigns NLS/KdV/HillRealGapIntegrals)
modules+=(NLS/ComplexAnalysis/AnalyticDiscSquareRoot NLS/ComplexAnalysis/AnalyticTwoZeroRoot NLS/ComplexAnalysis/TwoZeroDeflation NLS/ComplexAnalysis/TwoZeroRootEndpointBound NLS/KdV/HillL2GapCutRoots NLS/KdV/HillL2GapCutPrimitives NLS/KdV/HillL2GapCutBoundary NLS/KdV/HillL2CollapsedGapMoments)
modules+=(NLS/ComplexAnalysis/TraceRootPrimitive NLS/ComplexAnalysis/RealCutConjugation NLS/KdV/HillL2NormalizedCutPrimitive NLS/KdV/HillL2CutPrimitiveReflection NLS/KdV/HillL2CutPrimitiveEndpointValues)
modules+=(NLS/ComplexAnalysis/LogarithmStripNormalization NLS/KdV/HillL2RealSourcePhase NLS/KdV/HillL2CutRealPhase NLS/KdV/HillL2CutEndpointNormalization)
modules+=(NLS/ComplexAnalysis/GapPrimitiveSquare NLS/ComplexAnalysis/CoshSquareCoordinate NLS/KdV/HillL2CutPrimitiveSquare NLS/KdV/HillL2CutSquareTrace NLS/KdV/HillL2CutSquareDeflation)
modules+=(NLS/ComplexAnalysis/RealTwoZeroUnit NLS/ComplexAnalysis/RealEndpointRootBoundary NLS/KdV/HillL2CutPrimitiveUnit NLS/KdV/HillL2CutUnitOrientation NLS/KdV/HillL2GapBoundaryValues)
for module in "${modules[@]}"; do
  for suffix in olean olean.private olean.server; do
    if [[ -L "$build_root/$module.$suffix" ]]; then
      rm -- "$build_root/$module.$suffix"
    fi
  done
  lean -DautoImplicit=false -DwarningAsError=true -o "$build_root/$module.olean" "$module.lean"
done
lean -DautoImplicit=false -DwarningAsError=true coverage/articles/kdv-estimates/CheckPrivateAxioms.lean
