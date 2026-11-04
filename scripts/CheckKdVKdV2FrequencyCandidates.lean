import NLS.KdV.HillHminusOneMiuraNormalizedIdentification
import NLS.KdV.HillHminusOneOriginalNormalizedPeriods
import NLS.KdV.HillHminusOneOriginalContourBands
import NLS.KdV.HillHminusOneOriginalContourRoots
import NLS.KdV.HillHminusOneCanonicalCriticalCompatibility
import NLS.KdV.HillHminusOneCriticalChartGerms
import NLS.KdV.CanonicalMiuraNumeratorRepresentation
import NLS.ComplexAnalysis.EntireCriticalHilbertBasis
import NLS.KdV.HillHminusOneMiuraEnergyPrincipalSeries
import NLS.ZakharovShabat.SourcePsiCriticalAbsoluteInterpolation
import NLS.KdV.HillHminusOneMiuraResidueHilbert
import NLS.KdV.HillHminusOneMiuraCriticalResidues
import NLS.KdV.HillHminusOneEnergyRootContinuationAgreement
import NLS.KdV.HillHminusOneMappedEnergyPeriods
import NLS.KdV.HillHminusOneMiuraEnergyRoot
import NLS.KdV.HillHminusOneMiuraEnergyPeriods
import NLS.ZakharovShabat.EvenPsiAntisymmetricPeriods
import NLS.KdV.HillHminusOneMiuraRootSymmetry
import NLS.ZakharovShabat.EvenDiscriminantCanonicalRoot
import NLS.KdV.HillHminusOneRealMiuraEnergyPsi
import NLS.KdV.HillHminusOneRealMiuraCharts
import NLS.ZakharovShabat.SourcePsiLemma12_11
import NLS.SequenceSpaces.PeriodOneRealMiuraCharts
import NLS.SequenceSpaces.PeriodOneMiuraConjugation
import NLS.ComplexAnalysis.EquivariantSmallQuadraticInverse
import NLS.KdV.HillHminusOneNormalizedFrequencySeries
import NLS.KdV.HillHminusOneFrequencyGapMajorant
import NLS.KdV.HillHminusOneCanonicalFrequencyGaps
import NLS.ComplexAnalysis.SquaredPairGapBound
import NLS.KdV.HillHminusOneTwoWeightedMomentBounds
import NLS.KdV.HillHminusOneNormalizedGapMomentBounds
import NLS.KdV.HillHminusOneCriticalPrimitivePeriods
import NLS.KdV.HillHminusOneGapPairUniqueness
import NLS.KdV.HillHminusOneWeightedCutPeriods
import NLS.ComplexAnalysis.CollapsedPowerPeriods
import NLS.KdV.HillHminusOneCriticalGapCutRoots
import NLS.KdV.HillHminusOneNormalizedMomentKernel
import NLS.KdV.HillHminusOneMomentKernel
import NLS.SequenceSpaces.QuadraticPoleKernel
import NLS.ComplexAnalysis.CriticalBasisPowerPeriods
import NLS.KdV.HillHminusOneTwoWeightedNormalizedMoments
import NLS.KdV.HillHminusOneCriticalGapLocalization
import NLS.KdV.HillHminusOneGapQuotientAsymptotics
import NLS.SequenceSpaces.AnalyticTwoWeightedInverseColumns
import NLS.KdV.HillHminusOneTwoWeightedPeriodInverse
import NLS.KdV.HillHminusOneNormalizedOddMoments
import NLS.KdV.HillHminusOneNormalizedMoments
import NLS.KdV.HillHminusOnePeriodEntries
import NLS.KdV.HillHminusOneCriticalNumerators
import NLS.KdV.HillHminusOneAnnulusCoverage
import NLS.KdV.ClassicalNormalizedFrequencySeries
import NLS.KdV.ClassicalTwoWeightedMomentBounds
import NLS.KdV.ClassicalNormalizedGapMomentBounds
import NLS.KdV.ClassicalCriticalPrimitivePeriods
import NLS.ComplexAnalysis.AnalyticCutContour
import NLS.ComplexAnalysis.SquaredCircleHomotopy
import NLS.KdV.ClassicalHillGapCutRoots
import NLS.KdV.ClassicalCriticalGapLocalization
import NLS.KdV.SquaredCoshCriticalDisc
import NLS.ComplexAnalysis.TwoZeroCriticalLocalization
import NLS.KdV.ClassicalHillGapQuotientAsymptotics
import NLS.KdV.ClassicalNormalizedMomentResolvent
import NLS.KdV.ClassicalNormalizedCollapsedMoments
import NLS.KdV.ClassicalNormalizedOddMoments
import NLS.KdV.ClassicalNormalizedProductConstant
import NLS.KdV.ClassicalNormalizedProductQuotient
import NLS.KdV.ClassicalCandidateRootProducts
import NLS.KdV.ClassicalNormalizedZeros
import NLS.KdV.ClassicalNormalizedResidues
import NLS.KdV.ClassicalWeightedNormalizedCoefficients
import NLS.KdV.ClassicalCriticalBasisProduct
import NLS.Dynamics.ActionDependentWeightedPhaseFlow
import NLS.Dynamics.FixedTimePhaseObstruction
import NLS.KdV.ClassicalUniformCriticalBasis
import NLS.KdV.ClassicalPeriodIntegrationByParts
import NLS.KdV.ClassicalPeriodInverse
import NLS.KdV.ClassicalNormalizedDifferentials
import NLS.KdV.ClassicalUniformPeriodBounds
import NLS.KdV.ClassicalUniformCriticalLocalization
import NLS.KdV.ClassicalCriticalTailAnalytic
import NLS.KdV.ClassicalFiniteNormalizedDifferentials
import NLS.KdV.FreeFrequencyPsi
import NLS.KdV.FrequencyPrimitiveContinuation
import NLS.KdV.FrequencySeries
import NLS.KdV.FrequencyMoments
import NLS.KdV.FrequencyContourDecomposition
import NLS.Articles.KdVKdV2Frequencies.SignedPhaseFlow
import NLS.Articles.KdVKdV2Frequencies.MassPhaseObstruction
import NLS.Articles.KdVKdV2Frequencies.SmoothKdVIdentities
import NLS.Articles.KdVKdV2Frequencies.SignedMassDivergence
import NLS.Articles.KdVKdV2Frequencies.SignedMassInsertion
import NLS.Articles.KdVKdV2Frequencies.FixedTimeNonextension
import NLS.SequenceSpaces.HilbertEnergyDivergence
import Lean.Util.CollectAxioms

/-! Transitive axiom audit of the candidate and its imported NLS dependencies.
This deliberately imports specific modules, not the aggregate NLS library.
-/

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`NLS.ComplexAnalysis.BanachTaylorBounds,
    `NLS.SequenceSpaces.Convolution,
    `NLS.SequenceSpaces.Reflection,
    `NLS.SequenceSpaces.Multiplier,
    `NLS.SequenceSpaces.PositiveOddMultiplier,
    `NLS.ZakharovShabat.ClassicalHorizontalStripBounds,
    `NLS.SequenceSpaces.PositiveIndexWeight,
    `NLS.SequenceSpaces.PuncturedLattice,
    `NLS.SequenceSpaces.PositiveIndexPowerWeight,
    `NLS.SequenceSpaces.OperatorBasisExt,
    `NLS.SequenceSpaces.DiagonalIntertwining,
    `NLS.SequenceSpaces.BoundedCoordinateDifferentiable,
    `NLS.SequenceSpaces.CoordinateQuadraticDerivative,
    `NLS.SequenceSpaces.HolderEmbedding,
    `NLS.SequenceSpaces.BoundedCoordinateAnalytic,
    `NLS.ComplexAnalysis.JointSpectralDerivative,
    `NLS.ComplexAnalysis.AnalyticOperatorInverse,
    `NLS.SequenceSpaces.ConvolutionDominatedMatrix,
    `NLS.SequenceSpaces.LocallyBoundedRealization,
    `NLS.SequenceSpaces.TwoSequenceBound,
    `NLS.SequenceSpaces.FiniteHeadTailBound,
    `NLS.SequenceSpaces.AnalyticReciprocalTail,
    `NLS.SequenceSpaces.ConjugateDuality,
    `NLS.ComplexAnalysis.BilinearCircleIntegral,
    `NLS.SequenceSpaces.ConvolutionMatrixAnalytic,
    `NLS.SequenceSpaces.RankOneDominatedMatrix,
    `NLS.SequenceSpaces.MixedMajorantMatrix,
    `NLS.SequenceSpaces.ReciprocalSquareKernel,
    `NLS.ComplexAnalysis.AffineLoopHomotopy,
    `NLS.ComplexAnalysis.ParametricDividedDifference,
    `NLS.ComplexAnalysis.AnalyticImplicitBanachRoot,
    `NLS.ComplexAnalysis.AnalyticFinitePeriodNormalization,
    `NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot,
    `NLS.ComplexAnalysis.RightHalfPlaneSquareRoot,
    `NLS.ComplexAnalysis.EntireLimit,
    `NLS.ComplexAnalysis.LocalAnalyticSquareRoot,
    `NLS.ComplexAnalysis.SquareProductConvergence,
    `NLS.ComplexAnalysis.RemovableFactorConvergence,
    `NLS.ComplexAnalysis.RationalCircleIntegrationByParts,
    `NLS.ZakharovShabat.ContinuousPotentialL2Bound,
    `NLS.SequenceSpaces.FiniteModification,
    `NLS.ZakharovShabat.FreeDerivativeZeroCounts,
    `NLS.ZakharovShabat.CriticalPointLabeling,
    `NLS.ZakharovShabat.DiscriminantDerivativeProduct,
    `NLS.ZakharovShabat.UniformSmallCriticalDisplacements,
    `NLS.ZakharovShabat.UniformCanonicalPeriodicEndpoints,
    `NLS.ZakharovShabat.SourceCriticalRootRatioContourHomotopy,
    `NLS.ZakharovShabat.SourceDistantCriticalPointsAnalyticNeighborhood,
    `NLS.ZakharovShabat.NearFreeCriticalRelabeling,
    `NLS.KdV.ConstantUpperSpectralBridge,
    `NLS.KdV.ClassicalSpectralSymmetry,
    `NLS.KdV.ClassicalDiscriminant,
    `NLS.KdV.ClassicalLocalPrimitive,
    `NLS.KdV.ClassicalDiscriminantUniformVariation,
    `NLS.KdV.ClassicalFreePrimitive,
    `NLS.KdV.ClassicalHillFlow,
    `NLS.KdV.ClassicalHillSpectrum,
    `NLS.KdV.ClassicalSourcePrimitive,
    `NLS.ComplexAnalysis.NestedCircleHomotopy,
    `NLS.KdV.ClassicalSpectralEmbedding,
    `NLS.KdV.ClassicalContourCoverage,
    `NLS.KdV.ActionHamiltonianMoments,
    `NLS.KdV.ClassicalContourMoments,
    `NLS.KdV.ClassicalHighContourMoments,
    `NLS.ComplexAnalysis.AnalyticSquareDescent,
    `NLS.KdV.ClassicalBranchPrimitive,
    `NLS.SequenceSpaces.LocallyBoundedAnalyticSummation,
    `NLS.KdV.FrequencySeriesBounds,
    `NLS.KdV.FrequencySeries,
    `NLS.SequenceSpaces.NonnegativeEnergyDivergence,
    `NLS.SequenceSpaces.HilbertEnergyDivergence,
    `NLS.Dynamics.ActionDependentWeightedPhaseFlow,
    `NLS.Dynamics.FixedTimePhaseObstruction,
    `NLS.KdV.FrequencyMoments,
    `NLS.KdV.FreeFrequencyPsi,
    `NLS.KdV.FreeHighContourPeriods,
    `NLS.KdV.FreeContourUniformLowerBound,
    `NLS.KdV.ClassicalUniformRootBounds,
    `NLS.KdV.ClassicalUniformPrimitiveBounds,
    `NLS.KdV.ClassicalCriticalPointBranch,
    `NLS.KdV.ClassicalHighCriticalPoints,
    `NLS.KdV.HighEnergyContourSeparation,
    `NLS.KdV.HighEnergyDiscSeparation,
    `NLS.KdV.PositiveEnergyResolventKernel,
    `NLS.KdV.ClassicalCriticalNumerator,
    `NLS.KdV.ClassicalUniformCriticalBasis,
    `NLS.KdV.ClassicalCriticalTailAnalytic,
    `NLS.KdV.ClassicalUniformCriticalLocalization,
    `NLS.KdV.ClassicalCriticalPeriods,
    `NLS.KdV.ClassicalFiniteNormalizedDifferentials,
    `NLS.KdV.ClassicalUniformPeriodEntries,
    `NLS.KdV.ClassicalPeriodIntegrationByParts,
    `NLS.KdV.ClassicalUniformPeriodBounds,
    `NLS.KdV.ClassicalAllContourPeriods,
    `NLS.KdV.ClassicalAllContourPeriodBounds,
    `NLS.KdV.ClassicalPeriodOperator,
    `NLS.KdV.ClassicalPeriodInverse,
    `NLS.KdV.ClassicalWeightedPeriodOperator,
    `NLS.KdV.ClassicalTwoWeightedPeriodOperator,
    `NLS.KdV.ClassicalWeightedPeriodInverse,
    `NLS.KdV.ClassicalTwoWeightedPeriodInverse,
    `NLS.KdV.ClassicalNumeratorHilbert,
    `NLS.KdV.ClassicalHilbertPeriod,
    `NLS.KdV.ClassicalNormalizedDifferentials,
    `NLS.KdV.ClassicalWeightedNormalizedCoefficients,
    `NLS.KdV.ClassicalTwoWeightedNormalizedCoefficients,
    `NLS.KdV.ClassicalNormalizedResidues,
    `NLS.KdV.ClassicalCandidateZeros,
    `NLS.SequenceSpaces.CompactPuncturedKernel,
    `NLS.KdV.ClassicalCandidateResolvents,
    `NLS.KdV.ClassicalNormalizedZeroMap,
    `NLS.KdV.ClassicalNormalizedRootBranches,
    `NLS.KdV.ClassicalNormalizedZeroIdentity,
    `NLS.KdV.ClassicalNormalizedZeros,
    `NLS.KdV.ClassicalSignedCriticalProduct,
    `NLS.KdV.ClassicalCandidateNumeratorUnits,
    `NLS.KdV.ClassicalNormalizedZeroFactorization,
    `NLS.KdV.ClassicalNormalizedZeroDerivative,
    `NLS.KdV.ClassicalNormalizedSimpleZeros,
    `NLS.ZakharovShabat.SourceGapInterpolationProduct,
    `NLS.KdV.ClassicalCandidateRootProducts,
    `NLS.ComplexAnalysis.CauchyFiniteHoles,
    `NLS.ComplexAnalysis.OddSquareDescent,
    `NLS.ZakharovShabat.PairedEnergyProduct,
    `NLS.ZakharovShabat.SourcePsiRootResolventExterior,
    `NLS.ZakharovShabat.PairedEnergyResolventExterior,
    `NLS.ZakharovShabat.SingleSpectralProductRatioExterior,
    `NLS.ZakharovShabat.PairedEnergyZeros,
    `NLS.ZakharovShabat.OmittedPairedEnergyProduct,
    `NLS.KdV.ClassicalCriticalEnergyProduct,
    `NLS.KdV.ClassicalCriticalBasisProduct,
    `NLS.KdV.ClassicalCandidateEnergyProducts,
    `NLS.ComplexAnalysis.FilledSimpleQuotient,
    `NLS.KdV.ClassicalNormalizedProductQuotient,
    `NLS.KdV.ClassicalNormalizedResolventExterior,
    `NLS.KdV.ClassicalNormalizedProductAsymptotics,
    `NLS.ComplexAnalysis.EntireCircleDecay,
    `NLS.ZakharovShabat.CentralCircleThresholds,
    `NLS.KdV.ClassicalNormalizedProductConstant,
    `NLS.KdV.FrequencyPrimitiveContinuation,
    `NLS.KdV.FrequencyContourDecomposition,
    `NLS.Articles.KdVKdV2Frequencies.SignedPhaseFlow,
    `NLS.Articles.KdVKdV2Frequencies.MassPhaseObstruction,
    `NLS.Articles.KdVKdV2Frequencies.SmoothKdVIdentities,
    `NLS.Articles.KdVKdV2Frequencies.SignedMassDivergence,
    `NLS.Articles.KdVKdV2Frequencies.SignedMassInsertion,
    `NLS.Articles.KdVKdV2Frequencies.FixedTimeNonextension,
    `NLS.KdV.ClassicalCoshStripControl,
    `NLS.KdV.ClassicalHillDiscAsymptotics,
    `NLS.KdV.ClassicalHillHighTracePhase,
    `NLS.KdV.ClassicalHillSmallDiscTrace,
    `NLS.KdV.ClassicalHillSmallGapCoverage,
    `NLS.ZakharovShabat.ClassicalSolutionInjectivity,
    `NLS.KdV.ClassicalHillGreen,
    `NLS.KdV.ClassicalHighGapPairs,
    `NLS.KdV.ClassicalHillReality,
    `NLS.KdV.ClassicalHillConjugation,
    `NLS.ComplexAnalysis.ContinuousSquareRootPath,
    `NLS.KdV.ClassicalHillPrimitiveSheets,
    `NLS.KdV.ClassicalHillPrimitiveReflection,
    `NLS.KdV.ClassicalHillBandNormalization,
    `NLS.KdV.ClassicalHillHighPrimitiveStrip,
    `NLS.KdV.ClassicalHillHighEndpointNormalization,
    `NLS.KdV.ClassicalHillSquaredPrimitiveMatching,
    `NLS.KdV.ClassicalHillWholeGapSquares,
    `NLS.KdV.ClassicalHillAnnulusCoverage,
    `NLS.KdV.ClassicalHillWholeGapQuotients,
    `NLS.KdV.ClassicalNormalizedMoments,
    `NLS.KdV.ClassicalHillOddDifferentialMoments,
    `NLS.KdV.ClassicalHillLowOddDifferentialMoments,
    `NLS.KdV.ClassicalNormalizedOddMoments,
    `NLS.ComplexAnalysis.TwoRootQuotientDiscBound,
    `NLS.ComplexAnalysis.TwoZeroDeflation,
    `NLS.KdV.ClassicalHillGapQuotients,
    `NLS.ComplexAnalysis.AnalyticDiscSquareRoot,
    `NLS.KdV.ClassicalHillCollapsedDifferentialMoments,
    `NLS.KdV.ClassicalNormalizedCollapsedMoments,
    `NLS.KdV.ClassicalCriticalResolvent,
    `NLS.ComplexAnalysis.CirclePowerIntegrationByParts,
    `NLS.KdV.ClassicalNormalizedMomentResolvent,
    `NLS.ComplexAnalysis.AnalyticLocalLipschitz,
    `NLS.KdV.ClassicalHillFreeSquareComparison,
    `NLS.ComplexAnalysis.NormalizedSquareRootBounds,
    `NLS.KdV.ClassicalHighGapFamilies,
    `NLS.KdV.ClassicalHillGapQuotientAsymptotics,
    `NLS.ComplexAnalysis.TwoZeroCriticalLocalization,
    `NLS.KdV.SquaredCoshCriticalDisc,
    `NLS.KdV.ClassicalCriticalGapLocalization,
    `NLS.KdV.ClassicalHillGapScaleBounds,
    `NLS.ComplexAnalysis.AnalyticTwoZeroRoot,
    `NLS.KdV.ClassicalHillGapCutRoots,
    `NLS.ComplexAnalysis.SquaredCircleHomotopy,
    `NLS.ComplexAnalysis.AnalyticCutContour,
    `NLS.KdV.ClassicalHillWeightedCutPeriods,
    `NLS.KdV.WeightedCutGapBounds,
    `NLS.KdV.ClassicalCriticalPrimitivePeriods,
    `NLS.SequenceSpaces.HilbertCoordinateRemainder,
    `NLS.KdV.ClassicalNormalizedGapMomentBounds,
    `NLS.SequenceSpaces.DiagonalBilinearPairing,
    `NLS.KdV.ClassicalTwoWeightedMomentBounds,
    `NLS.ZakharovShabat.CanonicalWeightedGapSummability,
    `NLS.KdV.ClassicalFrequencyGapMajorant,
    `NLS.SequenceSpaces.AnalyticTailSummation,
    `NLS.KdV.ClassicalNormalizedFrequencySeries,
    `NLS.FunctionalAnalysis.PeriodicIntegrationByParts,
    `NLS.MKdV.MiuraClassicalSolution,
    `NLS.SequenceSpaces.ConjugateReflection,
    `NLS.MKdV.SobolevMiuraPotential,
    `NLS.FunctionalAnalysis.LinearVolterraFlow,
    `NLS.MKdV.QuasiHillDiscriminant,
    `NLS.MKdV.MiuraBoundaryTransfer,
    `NLS.ZakharovShabat.ClassicalVolterraTrace,
    `NLS.MKdV.QuasiHillZSComparison,
    `NLS.MKdV.QuasiHillJointAnalytic,
    `NLS.ComplexAnalysis.SourceDiscriminantPrimitive,
    `NLS.ZakharovShabat.ContinuousPotentialSource,
    `NLS.ZakharovShabat.SourceCanonicalRootRealBand,
    `NLS.MKdV.QuasiHillSourcePrimitive,
    `NLS.DifferentialPolynomial.UngradedIntegrationByParts,
    `NLS.DifferentialPolynomial.PowerSeriesDerivation,
    `NLS.DifferentialPolynomial.DifferentialRiccati,
    `NLS.DifferentialPolynomial.RiccatiResolvent,
    `NLS.DifferentialPolynomial.LogarithmicDerivative,
    `NLS.DifferentialPolynomial.MiuraRiccati,
    `NLS.DifferentialPolynomial.ConstructedRiccatiResolvent,
    `NLS.DifferentialPolynomial.RiccatiResolventNaturality,
    `NLS.DifferentialPolynomial.MultiJet,
    `NLS.ZakharovShabat.SourcePsiLemma12_11,
    `NLS.ZakharovShabat.SobolevHierarchySymmetries,
    `NLS.MKdV.HierarchyRestriction,
    `NLS.DifferentialPolynomial.RiccatiResolventParity,
    `NLS.ZakharovShabat.NLSRiccatiResolvent,
    `NLS.MKdV.MiuraHierarchyHamiltonians,
    `NLS.DifferentialPolynomial.PolynomialVariation,
    `NLS.DifferentialPolynomial.AlgebraicPolynomialVariation,
    `NLS.DifferentialPolynomial.EulerLagrange,
    `NLS.DifferentialPolynomial.IndependentJetVariation,
    `NLS.DifferentialPolynomial.RiccatiResolventVariation,
    `NLS.ZakharovShabat.NLSRiccatiResolventVariation,
    `NLS.FunctionalAnalysis.UnitIntervalMean,
    `NLS.DifferentialPolynomial.SmoothVariation,
    `NLS.ZakharovShabat.ClassicalNLSHierarchyVariation,
    `NLS.DifferentialPolynomial.EulerScalar,
    `NLS.Fourier.PeriodicVariationalUniqueness,
    `NLS.ZakharovShabat.NLSRiccatiResolventGradient,
    `NLS.MKdV.HierarchyGradientRecurrence,
    `NLS.MKdV.MiuraHierarchyFlowRestriction,
    `NLS.DifferentialPolynomial.EulerOrderBounds,
    `NLS.ZakharovShabat.SobolevPolynomialL2,
    `NLS.Fourier.CircleUnitCoefficients,
    `NLS.ZakharovShabat.SobolevPolynomialVariation,
    `NLS.ZakharovShabat.SobolevSourceCotangent,
    `NLS.ZakharovShabat.SobolevSmoothFirstVariation,
    `NLS.MKdV.SobolevMiuraHillHamiltonian,
    `NLS.MKdV.MiuraHillRiccatiRemainder,
    `NLS.Fourier.CircleBilinearMean,
    `NLS.ZakharovShabat.SobolevPolynomialEndpointMean,
    `NLS.ZakharovShabat.SobolevScalarSmoothDensity,
    `NLS.MKdV.NativeMiuraHillHamiltonian,
    `NLS.MKdV.QuasiHillPhysicalEquation,
    `NLS.MKdV.QuasiHillPhysicalUniqueness,
    `NLS.MKdV.PhysicalHillDiscriminant,
    `NLS.MKdV.MiuraHillHamiltonianTrace,
    `NLS.MKdV.MiuraHillSpectralBridge,
    `NLS.KdV.HillNLSPrimitivePathComparison,
    `NLS.MKdV.MiuraHillPrimitiveComparison,
    `NLS.MKdV.QuasiHillPrimitiveComparison,
    `NLS.MKdV.SobolevQuasiHill,
    `NLS.MKdV.SobolevMiuraPrimitive,
    `NLS.KdV.FreeHill,
    `NLS.KdV.HillComplement,
    `NLS.KdV.HillReduction,
    `NLS.KdV.HillSobolev,
    `NLS.KdV.HillPhysical,
    `NLS.KdV.HillFirstOrderReduction,
    `NLS.KdV.HillAnalytic,
    `NLS.KdV.HillWeightedCoefficients,
    `NLS.KdV.HillBilinearSymmetry,
    `NLS.KdV.HillSpectralLipschitz,
    `NLS.FunctionalAnalysis.TwoDimensionalDeterminant,
    `NLS.KdV.HillRootSeparation,
    `NLS.SequenceSpaces.WeightedInsertion,
    `NLS.KdV.HillPeriodOnePotential,
    `NLS.KdV.HillL2SpectralCriterion,
    `NLS.KdV.HillClassicalIdentification,
    `NLS.FunctionalAnalysis.AbsoluteContinuityTranslation,
    `NLS.KdV.HillFullPeriod,
    `NLS.FunctionalAnalysis.LinearVolterraLinearity,
    `NLS.KdV.ClassicalHillMultipliers,
    `NLS.KdV.HillDiscriminantNecessity,
    `NLS.KdV.HillDiscriminantComparison,
    `NLS.ComplexAnalysis.EntireEvenSquareDescent,
    `NLS.KdV.HillL2EnergyDiscriminant,
    `NLS.MKdV.MiuraL2HillDiscriminant,
    `NLS.SequenceSpaces.PeriodOneMassResolvent,
    `NLS.SequenceSpaces.PeriodOneMiuraQuadratic,
    `NLS.ComplexAnalysis.SmallQuadraticInverse,
    `NLS.SequenceSpaces.PeriodOneMiuraCharts,
    `NLS.SequenceSpaces.PeriodOneMiuraRegularity,
    `NLS.SequenceSpaces.PeriodOneMiuraShift,
    `NLS.KdV.HillL2ConstantShift,
    `NLS.KdV.HillMiuraL2Discriminant,
    `NLS.SequenceSpaces.PeriodOneHminusOneDensity,
    `NLS.KdV.HillHminusOneDiscriminant,
    `NLS.ComplexAnalysis.ShiftedSquareRootBounds,
    `NLS.KdV.HillFreeEnergyShift,
    `NLS.KdV.HillHminusOneDiscAsymptotics,
    `NLS.KdV.HillWeightIndependence,
    `NLS.KdV.HillLocalization,
    `NLS.KdV.HillZeroCount,
    `NLS.ComplexAnalysis.ZeroCountHomotopy,
    `NLS.ComplexAnalysis.TwoZeroOrderComparison,
    `NLS.KdV.HillCharacteristicZeros,
    `NLS.KdV.HillRealSpectrum,
    `NLS.ComplexAnalysis.TracePrimitiveContinuation,
    `NLS.KdV.HillL2SourcePrimitive,
    `NLS.ComplexAnalysis.TracePrimitiveFunctoriality,
    `NLS.KdV.HillHminusOneSourcePrimitive,
    `NLS.KdV.HillHminusOneSmallGapCoverage,
    `NLS.KdV.HillHminusOneAnnulusCoverage,
    `NLS.ComplexAnalysis.AnalyticSimpleCriticalBranch,
    `NLS.KdV.HillHminusOneCriticalPoints,
    `NLS.KdV.HillHminusOneCriticalNumerators,
    `NLS.KdV.HillHminusOnePeriodEntries,
    `NLS.KdV.HillHminusOneCriticalControl,
    `NLS.KdV.HillHminusOneTraceControl,
    `NLS.ComplexAnalysis.LogarithmStripNormalization,
    `NLS.KdV.HillHminusOnePrimitiveStrip,
    `NLS.ComplexAnalysis.CoshStripBounds,
    `NLS.ZakharovShabat.SourceSection8SineEstimates,
    `NLS.ComplexAnalysis.CompactSliceBounds,
    `NLS.KdV.HillHminusOneUniformPrimitiveBounds,
    `NLS.ComplexAnalysis.CriticalBasisPeriodBounds,
    `NLS.KdV.HillHminusOnePeriodBounds,
    `NLS.KdV.HillHminusOnePeriodInverse,
    `NLS.KdV.HillHminusOneNumeratorHilbert,
    `NLS.KdV.HillHminusOneHilbertPeriod,
    `NLS.KdV.HillHminusOneNormalizedDifferentials,
    `NLS.KdV.HillHminusOneNormalizedMoments,
    `NLS.ComplexAnalysis.AnalyticImplicitUniqueness,
    `NLS.KdV.ClassicalRoughEmbedding,
    `NLS.KdV.ClassicalRoughCriticalCompatibility,
    `NLS.ComplexAnalysis.ParametricDividedDifferenceCongruence,
    `NLS.KdV.ClassicalRoughNormalizationCompatibility,
    `NLS.ComplexAnalysis.DenseLinearAnalyticUniqueness,
    `NLS.KdV.HillHminusOneNormalizedOddMoments,
    `NLS.KdV.HillHminusOneTwoWeightedPeriodOperator,
    `NLS.KdV.HillHminusOneTwoWeightedPeriodInverse,
    `NLS.KdV.HillHminusOneWholeGapSquares,
    `NLS.KdV.HillHminusOneFreeSquareComparison,
    `NLS.ComplexAnalysis.QuadraticClusterCount,
    `NLS.KdV.HillHminusOneHighGapPairs,
    `NLS.KdV.HillHminusOneGapQuotients,
    `NLS.KdV.HillHminusOneGapQuotientAsymptotics,
    `NLS.SequenceSpaces.AnalyticTwoWeightedInverseColumns,
    `NLS.KdV.HillHminusOneSmallCriticalControl,
    `NLS.KdV.HillHminusOneCriticalGapLocalization,
    `NLS.KdV.HillHminusOneTwoWeightedNormalizedMoments,
    `NLS.SequenceSpaces.QuadraticPoleKernel,
    `NLS.ComplexAnalysis.CriticalBasisPowerPeriods,
    `NLS.KdV.HillHminusOneMomentKernel,
    `NLS.KdV.HillHminusOneNormalizedMomentKernel,
    `NLS.ComplexAnalysis.CollapsedPowerPeriods,
    `NLS.KdV.HillHminusOneCriticalGapCutRoots,
    `NLS.KdV.HillHminusOneWeightedCutPeriods,
    `NLS.KdV.HillHminusOneGapPairUniqueness,
    `NLS.KdV.HillHminusOneCriticalPrimitivePeriods,
    `NLS.KdV.HillHminusOneNormalizedGapMomentBounds,
    `NLS.KdV.HillHminusOneTwoWeightedMomentBounds,
    `NLS.ComplexAnalysis.SquaredPairGapBound,
    `NLS.KdV.HillHminusOneCanonicalFrequencyGaps,
    `NLS.KdV.HillHminusOneFrequencyGapMajorant,
    `NLS.KdV.HillHminusOneNormalizedFrequencySeries,
    `NLS.ComplexAnalysis.EquivariantSmallQuadraticInverse,
    `NLS.SequenceSpaces.PeriodOneMiuraConjugation,
    `NLS.SequenceSpaces.PeriodOneRealMiuraCharts,
    `NLS.KdV.HillHminusOneRealMiuraCharts,
    `NLS.KdV.HillHminusOneRealMiuraSourcePsi,
    `NLS.ComplexAnalysis.ParametricOddSquareDescent,
    `NLS.KdV.HillHminusOneRealMiuraEnergyPsi,
    `NLS.ZakharovShabat.EvenDiscriminantPeriodicEndpoints,
    `NLS.ZakharovShabat.EvenDiscriminantCanonicalRoot,
    `NLS.ComplexAnalysis.NegatedCircleIntegral,
    `NLS.KdV.HillHminusOneMiuraRootSymmetry,
    `NLS.ZakharovShabat.SourceTheorem12_1,
    `NLS.ZakharovShabat.EvenPsiAntisymmetricPeriods,
    `NLS.KdV.HillHminusOneMiuraEnergyPeriods,
    `NLS.ZakharovShabat.EvenPositivePeriodCircle,
    `NLS.KdV.HillHminusOneMiuraEnergyRoot,
    `NLS.ComplexAnalysis.ShiftedSquaredCircle,
    `NLS.KdV.HillHminusOneMappedEnergyPeriods,
    `NLS.ComplexAnalysis.NonrealConnectedDomain,
    `NLS.ZakharovShabat.SourceHighShiftedRealBand,
    `NLS.KdV.HillHminusOneEnergyRootChartAgreement,
    `NLS.SequenceSpaces.PeriodOneRealScaling,
    `NLS.KdV.HillHminusOneRealSpectralExclusion,
    `NLS.KdV.HillHminusOneEnergyRootFreeAgreement,
    `NLS.KdV.HillHminusOneEnergyRootContinuationAgreement,
    `NLS.ComplexAnalysis.EvenSpectralDerivatives,
    `NLS.ZakharovShabat.EvenRealCanonicalCriticalPoints,
    `NLS.KdV.HillHminusOneRealCriticalEnergyGeometry,
    `NLS.ComplexAnalysis.SimpleZeroPrincipalCoefficient,
    `NLS.KdV.HillHminusOneMiuraCriticalResidues,
    `NLS.ZakharovShabat.SourcePsiCriticalQuotientExterior,
    `NLS.ZakharovShabat.SourcePsiCriticalInterpolation,
    `NLS.ComplexAnalysis.SimplePoleCircleResidue,
    `NLS.ZakharovShabat.SourcePsiCriticalResidueBounds,
    `NLS.KdV.HillHminusOneMiuraResidueHilbert,
    `NLS.ZakharovShabat.SourcePsiCriticalAbsoluteInterpolation,
    `NLS.KdV.HillHminusOneMiuraEnergyPrincipalSeries,
    `NLS.ComplexAnalysis.EntireCriticalHilbertBasis,
    `NLS.KdV.CanonicalMiuraNumeratorRepresentation,
    `NLS.ComplexAnalysis.SimpleRootGermUniqueness,
    `NLS.KdV.HillHminusOneCriticalChartIndependence,
    `NLS.KdV.HillHminusOneCriticalChartGerms,
    `NLS.KdV.FreeHillCriticalEnergies,
    `NLS.KdV.HillHminusOneCanonicalCriticalCompatibility,
    `NLS.KdV.HillHminusOneRealContinuationBands,
    `NLS.KdV.HillHminusOneOriginalContourRoots,
    `NLS.ZakharovShabat.SourceContourAdjacentBands,
    `NLS.KdV.HillHminusOneOriginalContourBands,
    `NLS.ComplexAnalysis.ShiftedSquaredCircleBandHomotopy,
    `NLS.KdV.HillHminusOneEnergyBands,
    `NLS.KdV.HillHminusOneOriginalNormalizedPeriods,
    `NLS.KdV.HillHminusOneMiuraNormalizedIdentification]
  let mut checked : Nat := 0
  let mut candidates : Nat := 0
  for (name, _) in (← getEnv).constants do
    let candidate := ((← findModuleOf? name).map modules.contains).getD false
    if (`NLS).isPrefixOf name || candidate then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      checked := checked + 1
      if candidate then
        candidates := candidates + 1
  if candidates == 0 then
    throwError "No candidate declarations found; the audit did not run."
  logInfo m!"Axiom audit passed: {candidates} candidate declarations; {checked} declarations total."
