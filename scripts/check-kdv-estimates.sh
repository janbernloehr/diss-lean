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
ensure_private_dir NLS/ZakharovShabat
ensure_private_dir NLS/DifferentialPolynomial
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
modules+=(NLS/ComplexAnalysis/RealGapEllipse NLS/ComplexAnalysis/RealGapEllipseHomotopy NLS/ComplexAnalysis/RealGapEllipseIntegral NLS/ComplexAnalysis/RealGapEllipseLimit NLS/ComplexAnalysis/RealCutCircleIntegral NLS/ComplexAnalysis/NestedCircleHomotopy NLS/ComplexAnalysis/AnalyticCutContour NLS/KdV/HillL2GapContourIntegral NLS/KdV/HillL2HighGapMoments)
modules+=(NLS/KdV/HillL2DiscAsymptotics NLS/ZakharovShabat/ContinuousPotentialL2Bound NLS/KdV/ClassicalSpectralEmbedding NLS/KdV/ClassicalHillSpectrum NLS/KdV/ClassicalSourcePrimitive NLS/KdV/ClassicalContourCoverage NLS/KdV/ClassicalHillDiscAsymptotics NLS/KdV/ClassicalHillHighTracePhase NLS/KdV/HillL2TraceControl NLS/ZakharovShabat/ClassicalSolutionInjectivity NLS/KdV/ClassicalHillGreen NLS/KdV/ClassicalHighGapPairs NLS/KdV/ClassicalHillReality NLS/KdV/ClassicalHillPrimitiveSheets NLS/KdV/ClassicalHillPrimitiveReflection NLS/KdV/ClassicalHillBandNormalization NLS/KdV/ClassicalHillHighPrimitiveStrip NLS/KdV/HillL2PrimitiveStrip NLS/KdV/ClassicalBranchPrimitive NLS/KdV/ClassicalCoshStripControl NLS/KdV/ClassicalHillSmallDiscTrace NLS/KdV/ClassicalHillSmallGapCoverage NLS/KdV/ClassicalHillHighEndpointNormalization NLS/KdV/ClassicalHillSquaredPrimitiveMatching NLS/KdV/ClassicalHillWholeGapSquares NLS/KdV/HillL2WholeGapSquares NLS/ComplexAnalysis/AnalyticLocalLipschitz NLS/KdV/ClassicalHillFreeSquareComparison NLS/KdV/HillL2FreeSquareComparison NLS/KdV/HillL2HighGapPairs NLS/KdV/HillL2SmallGapCoverage NLS/KdV/HillL2GapSquareFamilies NLS/KdV/HillL2GapQuotients NLS/ComplexAnalysis/NormalizedSquareRootBounds NLS/KdV/HillL2GapQuotientAsymptotics NLS/KdV/HillHighMomentComparison NLS/KdV/HillL2GapSquareIdentification NLS/KdV/HillRealGapUnitBound NLS/KdV/HillEventualActionGapBound NLS/KdV/HillWeightedRealActions)
modules+=(NLS/KdV/ActionHamiltonianMoments NLS/ComplexAnalysis/TracePrimitiveFunctoriality NLS/KdV/ClassicalL2PrimitiveAgreement NLS/ComplexAnalysis/PositiveRealPart NLS/KdV/HillL2HalfPlaneSheets NLS/ComplexAnalysis/UpperTracePrimitiveExtension NLS/KdV/HillL2RegularBoundary NLS/ComplexAnalysis/RealCoshTrace NLS/KdV/HillL2BoundaryGapProfile NLS/KdV/HillL2UpperCutAgreement)
modules+=(NLS/ComplexAnalysis/UpperLogarithmBoundary NLS/KdV/HillL2AllBoundaryLimits NLS/ComplexAnalysis/ParametricUpperLogarithmBoundary NLS/KdV/HillL2BoundaryLabelContinuity NLS/KdV/HillL2AllEndpointNormalization NLS/KdV/HillL2GlobalGapBoundaryValues NLS/KdV/HillL2BandContinuation)
modules+=(NLS/ComplexAnalysis/ClosedUpperExtension NLS/KdV/HillL2CutBounds NLS/ComplexAnalysis/RealGapDiscIsolation NLS/KdV/HillRealGapContours NLS/ComplexAnalysis/BoundedPuncturedCircleIntegral NLS/KdV/HillL2AllGapContourIntegrals NLS/KdV/HillL2RealCutDifferential NLS/KdV/HillL2RealContourMoments)
modules+=(NLS/ComplexAnalysis/BoundaryAnalyticCoordinate NLS/ComplexAnalysis/CoshSquareLocalCoordinate NLS/KdV/HillL2AllGapSquares NLS/ComplexAnalysis/ShiftedSquarePeriod NLS/KdV/HillL2SquareGapPeriods NLS/KdV/HillHierarchyMomentSummability NLS/KdV/HillL2EndpointContinuity NLS/KdV/HillL2GroundSquare)
modules+=(NLS/ComplexAnalysis/RealCenteredHoleGeometry NLS/KdV/HillFiniteBandCover NLS/KdV/HillOuterTraceGeometry NLS/ComplexAnalysis/FiniteCircleHoleDecomposition NLS/KdV/HillOuterTraceDomain NLS/KdV/HillFiniteTraceContour NLS/KdV/HillOuterTraceExhaustion NLS/KdV/HillOuterTraceLimit)
modules+=(NLS/ComplexAnalysis/UnimodularWeightedTraceError NLS/ZakharovShabat/ClassicalWeightedResidualStability NLS/ZakharovShabat/NLSWKBCarrierWeightedBounds NLS/ZakharovShabat/NLSWKBComparison NLS/ZakharovShabat/NLSWKBWeightedComparison NLS/ZakharovShabat/NLSHamiltonianDiscriminantAsymptotics NLS/ZakharovShabat/NLSHamiltonianWeightedAsymptotics NLS/KdV/RiccatiEnergy NLS/KdV/ClassicalTraceAsymptotics NLS/KdV/ClassicalWeightedTraceAsymptotics)
modules+=(NLS/ComplexAnalysis/LocalSinhComparison NLS/ComplexAnalysis/ContinuousIntervalBranch NLS/ComplexAnalysis/WeightedCoshInverse NLS/ComplexAnalysis/ImaginaryCoshInverse NLS/ComplexAnalysis/ConnectedPhaseControl NLS/KdV/HillL2BandPhase NLS/ZakharovShabat/FreeCosineZeroAudit NLS/ZakharovShabat/NLSHamiltonianPhasePolynomial NLS/KdV/HillL2BandAnchors NLS/KdV/HillFreeUpperArcs NLS/KdV/HillL2UpperArcAsymptotics)
modules+=(NLS/ComplexAnalysis/LaurentSquareRemainder NLS/ComplexAnalysis/UpperCircleReflection NLS/ComplexAnalysis/QuadraticContourCoefficient NLS/ComplexAnalysis/NonnegativeComplexSeries NLS/KdV/HillContinuousReality NLS/KdV/HillFreeCircleGeometry NLS/KdV/HillFreeTraceContour NLS/KdV/HillL2UpperSquareAsymptotics NLS/KdV/HillL2SquareCircleAsymptotics NLS/KdV/HillSmoothQuadraticTraceLimit NLS/KdV/HillSmoothQuadraticTrace)
modules+=(NLS/KdV/HillRealActionContinuity)
modules+=(NLS/SequenceSpaces/LocalSeriesContinuity NLS/KdV/HillActionTailBudget NLS/KdV/HillLocallyUniformActionTails NLS/KdV/HillWeightedActionContinuity)
modules+=(NLS/KdV/HillFinitePhysicalPotential NLS/KdV/HillRealWeightedTruncation NLS/KdV/HillL2QuadraticTrace)
modules+=(NLS/ComplexAnalysis/WeightedSquareRemainder NLS/ComplexAnalysis/EnergyContourCoefficient NLS/KdV/HillL2UpperEnergySquareAsymptotics NLS/KdV/HillL2EnergySquareCircleAsymptotics NLS/KdV/HillSmoothEnergyTraceLimit NLS/KdV/HillHighMomentSigns NLS/KdV/HillSmoothEnergyTrace)
modules+=(NLS/KdV/HillHierarchyMomentContinuity NLS/KdV/HillSobolevEnergy NLS/KdV/HillH1EnergyTrace)
modules+=(NLS/DifferentialPolynomial/PowerSeriesDerivation NLS/DifferentialPolynomial/DifferentialRiccati NLS/DifferentialPolynomial/LogarithmicDerivative NLS/DifferentialPolynomial/ScalarRiccatiLogarithm NLS/KdV/HillRiccatiHierarchy NLS/KdV/HillHierarchyPhase)
modules+=(NLS/DifferentialPolynomial/WeightedJetReduction NLS/KdV/HillRiccatiRemainder NLS/KdV/HillHamiltonianReduction NLS/KdV/HillHierarchyTraceCoefficient NLS/KdV/HillHierarchyReality NLS/KdV/HillSecondHamiltonian)
modules+=(NLS/DifferentialPolynomial/JetMajorants NLS/DifferentialPolynomial/ScalarInterpolationExponents NLS/KdV/HillSobolevHierarchy NLS/KdV/HillHamiltonianMonomials NLS/KdV/HillMonomialInterpolation NLS/KdV/HillHamiltonianAbsorption NLS/KdV/HillHamiltonianCoercivity)
modules+=(NLS/ComplexAnalysis/LaurentContourCoefficient NLS/KdV/HillHierarchyPhaseModel NLS/KdV/HillL2HierarchySquareAsymptotics NLS/KdV/HillSmoothHierarchyTraceLimit NLS/KdV/HillSmoothHierarchyTrace)
modules+=(NLS/KdV/HillIntegerSobolev NLS/KdV/HillSobolevTraceFamily NLS/KdV/HillSobolevHierarchyTrace)
modules+=(NLS/KdV/HillGlobalMomentBounds NLS/KdV/HillIntegerActionMoments NLS/KdV/HillSummedMomentComparison NLS/KdV/HillUniformMomentComparison)
modules+=(NLS/KdV/HillLowerSobolevTrace NLS/SequenceSpaces/TriangularHierarchyBounds NLS/KdV/HillInverseSobolevBound NLS/Articles/KdVEstimates/InverseIntegerEstimate)
modules+=(NLS/KdV/HillNativeIntegerLower NLS/KdV/HillHamiltonianNormBounds NLS/KdV/HillHamiltonianConvolutionBounds NLS/KdV/HillForwardSobolevBound NLS/Articles/KdVEstimates/IntegerEstimates)
modules+=(NLS/KdV/HillPhysicalIntegerActions NLS/Articles/KdVEstimates/PhysicalIntegerEstimates NLS/KdV/HillActionSquareBound)
modules+=(NLS/ComplexAnalysis/EndpointRootBounds NLS/KdV/HillCanonicalEnergyRootProduct)
modules+=(NLS/KdV/HillEnergyRootAnalytic NLS/ComplexAnalysis/ComplexSquareRootShift NLS/KdV/HillEnergyFrequencyBounds)
modules+=(NLS/ComplexAnalysis/AnalyticSquarePullback NLS/KdV/HillSignedEnergyLabels)
modules+=(NLS/SequenceSpaces/IntegerSymmetricSums NLS/ComplexAnalysis/RealSquareRootCensus NLS/KdV/HillCentralEnergyLabeling)
modules+=(NLS/ZakharovShabat/PeriodicEndpointCandidates NLS/KdV/HillEnergyEndpointLabeling NLS/KdV/HillEnergyRadicandProduct)
modules+=(NLS/ComplexAnalysis/RealCutConnected NLS/ComplexAnalysis/RealEndpointRootSigns NLS/KdV/HillEnergyRootIdentification)
modules+=(NLS/ComplexAnalysis/DerivativeSquarePullbackOrder NLS/KdV/HillEnergyPolynomialLimits NLS/KdV/HillGapCriticalPoints NLS/KdV/HillCriticalFrequencyBridge NLS/Articles/KdVEstimates/ArnoldIntegerEstimates)
modules+=(NLS/KdV/HillCriticalCentralCensus NLS/KdV/HillSignedCriticalFrequencies NLS/KdV/HillEnergyCriticalProduct NLS/KdV/HillCriticalEnergyZeros)
modules+=(NLS/ComplexAnalysis/EndpointCriticalRatioBounds NLS/SequenceSpaces/NaturalSquareSeparation NLS/KdV/HillEnergyLogarithmicProduct NLS/KdV/HillOmittedEnergyCriticalProduct NLS/KdV/HillHighCriticalFactorBounds)
modules+=(NLS/ComplexAnalysis/RealCriticalProducts NLS/SequenceSpaces/PositiveQuotientProducts NLS/ComplexAnalysis/RealGapArcsineIntegral NLS/KdV/HillEnergyChiPositivity NLS/KdV/HillLowCriticalProductBound NLS/KdV/HillChiActionFormula)
modules+=(NLS/SequenceSpaces/NonnegativeSeriesCauchySchwarz NLS/SequenceSpaces/WeightedSquareSums NLS/SequenceSpaces/QuadraticSeparationTail NLS/ComplexAnalysis/ProductExponentialBound NLS/SequenceSpaces/WeightedCutoffPowers NLS/SequenceSpaces/SpectralWeightFixedShift NLS/KdV/HillCriticalProductBounds NLS/KdV/HillWeightedCriticalTail)
modules+=(NLS/KdV/HillUniformActionGapBound)
modules+=(NLS/SequenceSpaces/SpectralWeightProduct NLS/SequenceSpaces/SpectralWeightCeilingCutoff NLS/SequenceSpaces/QuadraticCutoffRounding NLS/KdV/HillWeightedActionHead NLS/KdV/HillWeightedActionEstimate NLS/Articles/KdVEstimates/WeightedActionEstimate NLS/KdV/HillL2DirichletCharacteristic)
modules+=(NLS/FunctionalAnalysis/UnitCurveIntegral NLS/ComplexAnalysis/ScalarStateMass NLS/ZakharovShabat/L2SolutionNonvanishing NLS/KdV/HillL2StateCurve NLS/KdV/HillL2GreenIdentity NLS/KdV/HillDirichletReality NLS/KdV/HillStateMonodromy NLS/KdV/HillDirichletBands)
modules+=(NLS/FunctionalAnalysis/UnitComplexCurveIntegral NLS/ComplexAnalysis/ScalarStateCrossMass NLS/ComplexAnalysis/QuadraticPuncturedLimit NLS/KdV/HillDirichletLagrange NLS/KdV/HillDirichletSimplicity NLS/KdV/HillDirichletRootBranches NLS/KdV/HillFreeDirichlet NLS/ComplexAnalysis/ClosedIntervalRoots)
modules+=(NLS/ComplexAnalysis/PositiveZeroUniqueness NLS/KdV/HillDirichletGapExistence NLS/KdV/HillDirichletGapUniqueness NLS/KdV/HillDirichletLabels NLS/KdV/HillDirichletLabelContinuity NLS/KdV/HillDirichletSlope NLS/KdV/HillDirichletNormingData)
modules+=(NLS/KdV/HillDirichletAnalyticLabels NLS/KdV/HillDirichletAnalyticNorming NLS/KdV/HillDirichletBranchDerivatives NLS/KdV/HillDirichletPotentialDerivative NLS/KdV/HillDirichletKernelNormalization NLS/KdV/HillDirichletGradients NLS/KdV/ClassicalHillDirichletBrackets)
modules+=(NLS/ComplexAnalysis/RealEnergySquareRoot NLS/KdV/HillStateJointContinuity NLS/KdV/HillRealPeriodOneTruncation NLS/ComplexAnalysis/ScalarStateSquaredPairing NLS/KdV/HillDirichletSquaredPairing NLS/KdV/HillDirichletGradientCurves NLS/KdV/HillDirichletGardnerBrackets NLS/KdV/HillDirichletGradientH1)
modules+=(NLS/KdV/ClassicalHillMixedPairings NLS/ComplexAnalysis/ScalarStateMixedPairing NLS/KdV/HillDirichletCosineData NLS/KdV/HillDirichletMixedPairings NLS/KdV/HillDirichletSlopePotentialDerivative NLS/KdV/HillDirichletSlopeVariation NLS/Fourier/ContinuousConstants NLS/KdV/HillDirichletSlopeShift NLS/KdV/HillLogNormingGradient)
modules+=(NLS/KdV/HillPhysicalDirectionPairing NLS/KdV/HillLogNormingCotangent NLS/KdV/HillLogNormingRegularity NLS/KdV/HillMixedGardnerBrackets NLS/KdV/ClassicalHillLogNormingBrackets NLS/KdV/HillLogNormingGardnerBrackets)
modules+=(NLS/KdV/HillAbelianRootBox NLS/KdV/HillAbelianNumeratorProduct NLS/KdV/HillAbelianProductContinuity NLS/KdV/HillAbelianProductZeros NLS/ComplexAnalysis/ContinuousCircleIntegral NLS/KdV/HillAbelianCandidatePeriods NLS/KdV/HillAbelianNormalizationProblem)
modules+=(NLS/KdV/HillFreeAbelianRoots NLS/KdV/HillFreeAbelianQuotient NLS/KdV/HillRealGapContourDiscs NLS/KdV/HillFreeAbelianNormalization NLS/KdV/HillAbelianCircleIntegrability NLS/KdV/HillFreeAbelianRootVariation NLS/KdV/HillFreeAbelianPeriodJacobian)
for module in "${modules[@]}"; do
  for suffix in olean olean.private olean.server; do
    if [[ -L "$build_root/$module.$suffix" ]]; then
      rm -- "$build_root/$module.$suffix"
    fi
  done
  lean -DautoImplicit=false -DwarningAsError=true -o "$build_root/$module.olean" "$module.lean"
done
lean -DautoImplicit=false -DwarningAsError=true coverage/articles/kdv-estimates/CheckPrivateAxioms.lean
