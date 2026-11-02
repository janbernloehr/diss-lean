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
    `NLS.KdV.ClassicalNormalizedFrequencySeries]
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
