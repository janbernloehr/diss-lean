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
  NLS/ComplexAnalysis/AffineLoopHomotopy
  NLS/ComplexAnalysis/ParametricDividedDifference
  NLS/ComplexAnalysis/AnalyticImplicitBanachRoot
  NLS/ComplexAnalysis/AnalyticFinitePeriodNormalization
  NLS/ComplexAnalysis/PrescribedAnalyticSquareRoot
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
  NLS/ZakharovShabat/UniformSmallCriticalDisplacements
  NLS/ZakharovShabat/UniformCanonicalPeriodicEndpoints
  NLS/ZakharovShabat/SourceCriticalRootRatioContourHomotopy
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
  NLS/ComplexAnalysis/NestedCircleHomotopy
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
  NLS/KdV/ClassicalNormalizedCollapsedMoments
  NLS/KdV/ClassicalCriticalResolvent
  NLS/ComplexAnalysis/CirclePowerIntegrationByParts
  NLS/KdV/ClassicalNormalizedMomentResolvent
  NLS/ComplexAnalysis/AnalyticLocalLipschitz
  NLS/KdV/ClassicalHillFreeSquareComparison
  NLS/ComplexAnalysis/NormalizedSquareRootBounds
  NLS/KdV/ClassicalHighGapFamilies
  NLS/KdV/ClassicalHillGapQuotientAsymptotics
  NLS/ComplexAnalysis/TwoZeroCriticalLocalization
  NLS/KdV/SquaredCoshCriticalDisc
  NLS/KdV/ClassicalCriticalGapLocalization
  NLS/KdV/ClassicalHillGapScaleBounds
  NLS/ComplexAnalysis/AnalyticTwoZeroRoot
  NLS/KdV/ClassicalHillGapCutRoots
  NLS/ComplexAnalysis/SquaredCircleHomotopy
  NLS/ComplexAnalysis/AnalyticCutContour
  NLS/KdV/ClassicalHillWeightedCutPeriods
  NLS/KdV/WeightedCutGapBounds
  NLS/KdV/ClassicalCriticalPrimitivePeriods
  NLS/SequenceSpaces/HilbertCoordinateRemainder
  NLS/KdV/ClassicalNormalizedGapMomentBounds
  NLS/SequenceSpaces/DiagonalBilinearPairing
  NLS/KdV/ClassicalTwoWeightedMomentBounds
  NLS/ZakharovShabat/CanonicalWeightedGapSummability
  NLS/KdV/ClassicalFrequencyGapMajorant
  NLS/SequenceSpaces/AnalyticTailSummation
  NLS/KdV/ClassicalNormalizedFrequencySeries
  NLS/FunctionalAnalysis/PeriodicIntegrationByParts
  NLS/MKdV/MiuraClassicalSolution
  NLS/SequenceSpaces/ConjugateReflection
  NLS/MKdV/SobolevMiuraPotential
  NLS/FunctionalAnalysis/LinearVolterraFlow
  NLS/MKdV/QuasiHillDiscriminant
  NLS/MKdV/MiuraBoundaryTransfer
  NLS/ZakharovShabat/ClassicalVolterraTrace
  NLS/MKdV/QuasiHillZSComparison
  NLS/MKdV/QuasiHillJointAnalytic
  NLS/ComplexAnalysis/SourceDiscriminantPrimitive
  NLS/ZakharovShabat/ContinuousPotentialSource
  NLS/ZakharovShabat/SourceCanonicalRootRealBand
  NLS/MKdV/QuasiHillSourcePrimitive
  NLS/DifferentialPolynomial/UngradedIntegrationByParts
  NLS/DifferentialPolynomial/PowerSeriesDerivation
  NLS/DifferentialPolynomial/DifferentialRiccati
  NLS/DifferentialPolynomial/RiccatiResolvent
  NLS/DifferentialPolynomial/LogarithmicDerivative
  NLS/DifferentialPolynomial/MiuraRiccati
  NLS/DifferentialPolynomial/ConstructedRiccatiResolvent
  NLS/DifferentialPolynomial/RiccatiResolventNaturality
  NLS/DifferentialPolynomial/MultiJet
  NLS/ZakharovShabat/SourcePsiLemma12_11
  NLS/ZakharovShabat/SobolevHierarchySymmetries
  NLS/MKdV/HierarchyRestriction
  NLS/DifferentialPolynomial/RiccatiResolventParity
  NLS/ZakharovShabat/NLSRiccatiResolvent
  NLS/MKdV/MiuraHierarchyHamiltonians
  NLS/DifferentialPolynomial/PolynomialVariation
  NLS/DifferentialPolynomial/AlgebraicPolynomialVariation
  NLS/DifferentialPolynomial/EulerLagrange
  NLS/DifferentialPolynomial/IndependentJetVariation
  NLS/DifferentialPolynomial/RiccatiResolventVariation
  NLS/ZakharovShabat/NLSRiccatiResolventVariation
  NLS/FunctionalAnalysis/UnitIntervalMean
  NLS/DifferentialPolynomial/SmoothVariation
  NLS/ZakharovShabat/ClassicalNLSHierarchyVariation
  NLS/DifferentialPolynomial/EulerScalar
  NLS/Fourier/PeriodicVariationalUniqueness
  NLS/ZakharovShabat/NLSRiccatiResolventGradient
  NLS/MKdV/HierarchyGradientRecurrence
  NLS/MKdV/MiuraHierarchyFlowRestriction
  NLS/DifferentialPolynomial/EulerOrderBounds
  NLS/ZakharovShabat/SobolevPolynomialL2
  NLS/Fourier/CircleUnitCoefficients
  NLS/ZakharovShabat/SobolevPolynomialVariation
  NLS/ZakharovShabat/SobolevSourceCotangent
  NLS/ZakharovShabat/SobolevSmoothFirstVariation
  NLS/MKdV/SobolevMiuraHillHamiltonian
  NLS/MKdV/MiuraHillRiccatiRemainder
  NLS/Fourier/CircleBilinearMean
  NLS/ZakharovShabat/SobolevPolynomialEndpointMean
  NLS/ZakharovShabat/SobolevScalarSmoothDensity
  NLS/MKdV/NativeMiuraHillHamiltonian
  NLS/MKdV/QuasiHillPhysicalEquation
  NLS/MKdV/QuasiHillPhysicalUniqueness
  NLS/MKdV/PhysicalHillDiscriminant
  NLS/MKdV/MiuraHillHamiltonianTrace
  NLS/MKdV/MiuraHillSpectralBridge
  NLS/KdV/HillNLSPrimitivePathComparison
  NLS/MKdV/MiuraHillPrimitiveComparison
  NLS/MKdV/QuasiHillPrimitiveComparison
  NLS/MKdV/SobolevQuasiHill
  NLS/MKdV/SobolevMiuraPrimitive
  NLS/KdV/FreeHill
  NLS/KdV/HillComplement
  NLS/KdV/HillReduction
  NLS/KdV/HillSobolev
  NLS/KdV/HillPhysical
  NLS/KdV/HillFirstOrderReduction
  NLS/KdV/HillAnalytic
  NLS/KdV/HillWeightedCoefficients
  NLS/KdV/HillBilinearSymmetry
  NLS/KdV/HillSpectralLipschitz
  NLS/FunctionalAnalysis/TwoDimensionalDeterminant
  NLS/KdV/HillRootSeparation
  NLS/SequenceSpaces/WeightedInsertion
  NLS/KdV/HillPeriodOnePotential
  NLS/KdV/HillL2SpectralCriterion
  NLS/KdV/HillClassicalIdentification
  NLS/FunctionalAnalysis/AbsoluteContinuityTranslation
  NLS/KdV/HillFullPeriod
  NLS/FunctionalAnalysis/LinearVolterraLinearity
  NLS/KdV/ClassicalHillMultipliers
  NLS/KdV/HillDiscriminantNecessity
  NLS/KdV/HillDiscriminantComparison
  NLS/ComplexAnalysis/EntireEvenSquareDescent
  NLS/KdV/HillL2EnergyDiscriminant
  NLS/MKdV/MiuraL2HillDiscriminant
  NLS/SequenceSpaces/PeriodOneMassResolvent
  NLS/SequenceSpaces/PeriodOneMiuraQuadratic
  NLS/ComplexAnalysis/SmallQuadraticInverse
  NLS/SequenceSpaces/PeriodOneMiuraCharts
  NLS/SequenceSpaces/PeriodOneMiuraRegularity
  NLS/SequenceSpaces/PeriodOneMiuraShift
  NLS/KdV/HillL2ConstantShift
  NLS/KdV/HillMiuraL2Discriminant
  NLS/SequenceSpaces/PeriodOneHminusOneDensity
  NLS/KdV/HillHminusOneDiscriminant
  NLS/ComplexAnalysis/ShiftedSquareRootBounds
  NLS/KdV/HillFreeEnergyShift
  NLS/KdV/HillHminusOneDiscAsymptotics
  NLS/KdV/HillWeightIndependence
  NLS/KdV/HillLocalization
  NLS/KdV/HillZeroCount
  NLS/ComplexAnalysis/ZeroCountHomotopy
  NLS/ComplexAnalysis/TwoZeroOrderComparison
  NLS/KdV/HillCharacteristicZeros
  NLS/KdV/HillRealSpectrum
  NLS/ComplexAnalysis/TracePrimitiveContinuation
  NLS/KdV/HillL2SourcePrimitive
  NLS/ComplexAnalysis/TracePrimitiveFunctoriality
  NLS/KdV/HillHminusOneSourcePrimitive
  NLS/KdV/HillHminusOneSmallGapCoverage
  NLS/KdV/HillHminusOneAnnulusCoverage
  NLS/ComplexAnalysis/AnalyticSimpleCriticalBranch
  NLS/KdV/HillHminusOneCriticalPoints
  NLS/KdV/HillHminusOneCriticalNumerators
  NLS/KdV/HillHminusOnePeriodEntries
  NLS/KdV/HillHminusOneCriticalControl
  NLS/KdV/HillHminusOneTraceControl
  NLS/ComplexAnalysis/LogarithmStripNormalization
  NLS/KdV/HillHminusOnePrimitiveStrip
  NLS/ComplexAnalysis/CoshStripBounds
  NLS/ZakharovShabat/SourceSection8SineEstimates
  NLS/ComplexAnalysis/CompactSliceBounds
  NLS/KdV/HillHminusOneUniformPrimitiveBounds
  NLS/ComplexAnalysis/CriticalBasisPeriodBounds
  NLS/KdV/HillHminusOnePeriodBounds
  NLS/KdV/HillHminusOnePeriodInverse
  NLS/KdV/HillHminusOneNumeratorHilbert
  NLS/KdV/HillHminusOneHilbertPeriod
  NLS/KdV/HillHminusOneNormalizedDifferentials
  NLS/KdV/HillHminusOneNormalizedMoments
  NLS/ComplexAnalysis/AnalyticImplicitUniqueness
  NLS/KdV/ClassicalRoughEmbedding
  NLS/KdV/ClassicalRoughCriticalCompatibility
  NLS/ComplexAnalysis/ParametricDividedDifferenceCongruence
  NLS/KdV/ClassicalRoughNormalizationCompatibility
  NLS/ComplexAnalysis/DenseLinearAnalyticUniqueness
  NLS/KdV/HillHminusOneNormalizedOddMoments
  NLS/KdV/HillHminusOneTwoWeightedPeriodOperator
  NLS/KdV/HillHminusOneTwoWeightedPeriodInverse
  NLS/KdV/HillHminusOneWholeGapSquares
  NLS/KdV/HillHminusOneFreeSquareComparison
  NLS/ComplexAnalysis/QuadraticClusterCount
  NLS/KdV/HillHminusOneHighGapPairs
  NLS/KdV/HillHminusOneGapQuotients
  NLS/KdV/HillHminusOneGapQuotientAsymptotics
  NLS/SequenceSpaces/AnalyticTwoWeightedInverseColumns
  NLS/KdV/HillHminusOneSmallCriticalControl
  NLS/KdV/HillHminusOneCriticalGapLocalization
  NLS/KdV/HillHminusOneTwoWeightedNormalizedMoments
  NLS/SequenceSpaces/QuadraticPoleKernel
  NLS/ComplexAnalysis/CriticalBasisPowerPeriods
  NLS/KdV/HillHminusOneMomentKernel
  NLS/KdV/HillHminusOneNormalizedMomentKernel
  NLS/ComplexAnalysis/CollapsedPowerPeriods
  NLS/KdV/HillHminusOneCriticalGapCutRoots
  NLS/KdV/HillHminusOneWeightedCutPeriods
  NLS/KdV/HillHminusOneGapPairUniqueness
  NLS/KdV/HillHminusOneCriticalPrimitivePeriods
  NLS/KdV/HillHminusOneNormalizedGapMomentBounds
  NLS/KdV/HillHminusOneTwoWeightedMomentBounds
  NLS/ComplexAnalysis/SquaredPairGapBound
  NLS/KdV/HillHminusOneCanonicalFrequencyGaps
  NLS/KdV/HillHminusOneFrequencyGapMajorant
  NLS/KdV/HillHminusOneNormalizedFrequencySeries
  NLS/ComplexAnalysis/EquivariantSmallQuadraticInverse
  NLS/SequenceSpaces/PeriodOneMiuraConjugation
  NLS/SequenceSpaces/PeriodOneRealMiuraCharts
  NLS/KdV/HillHminusOneRealMiuraCharts
  NLS/KdV/HillHminusOneRealMiuraSourcePsi
  NLS/ComplexAnalysis/ParametricOddSquareDescent
  NLS/KdV/HillHminusOneRealMiuraEnergyPsi
  NLS/ZakharovShabat/EvenDiscriminantPeriodicEndpoints
  NLS/ZakharovShabat/EvenDiscriminantCanonicalRoot
  NLS/ComplexAnalysis/NegatedCircleIntegral
  NLS/KdV/HillHminusOneMiuraRootSymmetry
  NLS/ZakharovShabat/SourceTheorem12_1
  NLS/ZakharovShabat/EvenPsiAntisymmetricPeriods
  NLS/KdV/HillHminusOneMiuraEnergyPeriods
  NLS/ZakharovShabat/EvenPositivePeriodCircle
  NLS/KdV/HillHminusOneMiuraEnergyRoot
  NLS/ComplexAnalysis/ShiftedSquaredCircle
  NLS/KdV/HillHminusOneMappedEnergyPeriods
  NLS/ComplexAnalysis/NonrealConnectedDomain
  NLS/ZakharovShabat/SourceHighShiftedRealBand
  NLS/KdV/HillHminusOneEnergyRootChartAgreement
  NLS/SequenceSpaces/PeriodOneRealScaling
  NLS/KdV/HillHminusOneRealSpectralExclusion
  NLS/KdV/HillHminusOneEnergyRootFreeAgreement
  NLS/KdV/HillHminusOneEnergyRootContinuationAgreement
  NLS/ComplexAnalysis/EvenSpectralDerivatives
  NLS/ZakharovShabat/EvenRealCanonicalCriticalPoints
  NLS/KdV/HillHminusOneRealCriticalEnergyGeometry
  NLS/ComplexAnalysis/SimpleZeroPrincipalCoefficient
  NLS/KdV/HillHminusOneMiuraCriticalResidues
  NLS/ZakharovShabat/SourcePsiCriticalQuotientExterior
  NLS/ZakharovShabat/SourcePsiCriticalInterpolation
  NLS/ComplexAnalysis/SimplePoleCircleResidue
  NLS/ZakharovShabat/SourcePsiCriticalResidueBounds
  NLS/KdV/HillHminusOneMiuraResidueHilbert
  NLS/ZakharovShabat/SourcePsiCriticalAbsoluteInterpolation
  NLS/KdV/HillHminusOneMiuraEnergyPrincipalSeries
  NLS/ComplexAnalysis/EntireCriticalHilbertBasis
  NLS/KdV/CanonicalMiuraNumeratorRepresentation
  NLS/ComplexAnalysis/SimpleRootGermUniqueness
  NLS/KdV/HillHminusOneCriticalChartIndependence
  NLS/KdV/HillHminusOneCriticalChartGerms
  NLS/KdV/FreeHillCriticalEnergies
  NLS/KdV/HillHminusOneCanonicalCriticalCompatibility
  NLS/KdV/HillHminusOneRealContinuationBands
  NLS/KdV/HillHminusOneOriginalContourRoots
  NLS/ZakharovShabat/SourceContourAdjacentBands
  NLS/KdV/HillHminusOneOriginalContourBands)
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
