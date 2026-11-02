import NLS.Dynamics.ActionDependentWeightedPhaseFlow
import NLS.Dynamics.FixedTimePhaseObstruction
import NLS.KdV.ClassicalUniformCriticalBasis
import NLS.KdV.ClassicalPeriodIntegrationByParts
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
  let modules := #[`NLS.ZakharovShabat.ContinuousPotentialL2Bound,
    `NLS.ZakharovShabat.SourceDistantCriticalPointsAnalyticNeighborhood,
    `NLS.KdV.ClassicalSpectralEmbedding,
    `NLS.KdV.ClassicalContourCoverage,
    `NLS.KdV.ActionHamiltonianMoments,
    `NLS.KdV.ClassicalContourMoments,
    `NLS.KdV.ClassicalHighContourMoments,
    `NLS.KdV.ClassicalHighCriticalPoints,
    `NLS.KdV.HighEnergyContourSeparation,
    `NLS.KdV.ClassicalUniformCriticalBasis,
    `NLS.KdV.ClassicalCriticalTailAnalytic,
    `NLS.ComplexAnalysis.JointSpectralDerivative,
    `NLS.ComplexAnalysis.ParametricDividedDifference,
    `NLS.ComplexAnalysis.AnalyticFinitePeriodNormalization,
    `NLS.ComplexAnalysis.RightHalfPlaneSquareRoot,
    `NLS.ComplexAnalysis.RationalCircleIntegrationByParts,
    `NLS.KdV.ClassicalCriticalPointBranch,
    `NLS.KdV.ClassicalCriticalNumerator,
    `NLS.KdV.ClassicalCriticalPeriods,
    `NLS.KdV.ClassicalFiniteNormalizedDifferentials,
    `NLS.KdV.ClassicalUniformPeriodEntries,
    `NLS.KdV.ClassicalPeriodIntegrationByParts,
    `NLS.KdV.ClassicalHillFlow,
    `NLS.KdV.ClassicalHillSpectrum,
    `NLS.KdV.ClassicalSourcePrimitive,
    `NLS.KdV.ClassicalFreePrimitive,
    `NLS.KdV.FreeFrequencyPsi,
    `NLS.KdV.FreeHighContourPeriods,
    `NLS.KdV.ConstantUpperSpectralBridge,
    `NLS.KdV.ClassicalSpectralSymmetry,
    `NLS.KdV.ClassicalDiscriminant,
    `NLS.KdV.ClassicalLocalPrimitive,
    `NLS.KdV.ClassicalBranchPrimitive,
    `NLS.KdV.FrequencyPrimitiveContinuation,
    `NLS.SequenceSpaces.LocallyBoundedAnalyticSummation,
    `NLS.KdV.FrequencySeriesBounds,
    `NLS.KdV.FrequencySeries,
    `NLS.SequenceSpaces.NonnegativeEnergyDivergence,
    `NLS.SequenceSpaces.HilbertEnergyDivergence,
    `NLS.Dynamics.ActionDependentWeightedPhaseFlow,
    `NLS.Dynamics.FixedTimePhaseObstruction,
    `NLS.KdV.FrequencyMoments,
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
