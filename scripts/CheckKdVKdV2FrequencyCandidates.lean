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
    `NLS.ZakharovShabat.ClassicalHorizontalStripBounds,
    `NLS.SequenceSpaces.Multiplier,
    `NLS.SequenceSpaces.PositiveIndexWeight,
    `NLS.SequenceSpaces.PuncturedLattice,
    `NLS.SequenceSpaces.PositiveIndexPowerWeight,
    `NLS.SequenceSpaces.OperatorBasisExt,
    `NLS.SequenceSpaces.DiagonalIntertwining,
    `NLS.SequenceSpaces.HolderEmbedding,
    `NLS.SequenceSpaces.BoundedCoordinateAnalytic,
    `NLS.ComplexAnalysis.JointSpectralDerivative,
    `NLS.ComplexAnalysis.AnalyticOperatorInverse,
    `NLS.SequenceSpaces.ConvolutionDominatedMatrix,
    `NLS.SequenceSpaces.LocallyBoundedRealization,
    `NLS.SequenceSpaces.FiniteHeadTailBound,
    `NLS.SequenceSpaces.AnalyticReciprocalTail,
    `NLS.SequenceSpaces.ConjugateDuality,
    `NLS.ComplexAnalysis.BilinearCircleIntegral,
    `NLS.SequenceSpaces.ConvolutionMatrixAnalytic,
    `NLS.SequenceSpaces.RankOneDominatedMatrix,
    `NLS.SequenceSpaces.MixedMajorantMatrix,
    `NLS.SequenceSpaces.ReciprocalSquareKernel,
    `NLS.ComplexAnalysis.ParametricDividedDifference,
    `NLS.ComplexAnalysis.AnalyticFinitePeriodNormalization,
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
    `NLS.KdV.ClassicalSpectralEmbedding,
    `NLS.KdV.ClassicalContourCoverage,
    `NLS.KdV.ActionHamiltonianMoments,
    `NLS.KdV.ClassicalContourMoments,
    `NLS.KdV.ClassicalHighContourMoments,
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
    `NLS.KdV.ClassicalSignedCriticalProduct,
    `NLS.KdV.ClassicalCriticalEnergyProduct,
    `NLS.KdV.ClassicalCriticalBasisProduct,
    `NLS.KdV.FrequencyPrimitiveContinuation,
    `NLS.KdV.FrequencyContourDecomposition,
    `NLS.Articles.KdVKdV2Frequencies.SignedPhaseFlow,
    `NLS.Articles.KdVKdV2Frequencies.MassPhaseObstruction,
    `NLS.Articles.KdVKdV2Frequencies.SmoothKdVIdentities,
    `NLS.Articles.KdVKdV2Frequencies.SignedMassDivergence,
    `NLS.Articles.KdVKdV2Frequencies.SignedMassInsertion,
    `NLS.Articles.KdVKdV2Frequencies.FixedTimeNonextension]
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
