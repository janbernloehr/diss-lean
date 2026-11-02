import NLS.KdV.FreeHill
import NLS.KdV.HillComplement
import NLS.KdV.HillReduction
import NLS.KdV.HillSobolev
import NLS.KdV.HillPhysical
import NLS.KdV.HillAnalytic
import NLS.KdV.HillLocalization
import NLS.KdV.HillZeroCount
import NLS.KdV.HillWeightedCoefficients
import NLS.KdV.HillBilinearSymmetry
import NLS.FunctionalAnalysis.TwoDimensionalDeterminant
import NLS.KdV.HillSpectralLipschitz
import NLS.KdV.HillRootSeparation
import NLS.SequenceSpaces.WeightedInsertion
import NLS.SequenceSpaces.PositiveFourierTail
import NLS.SequenceSpaces.ReciprocalSquareTail
import NLS.KdV.HillPeriodOnePotential
import NLS.KdV.HillGapTail
import NLS.KdV.ConstantUpperSpectralBridge
import NLS.KdV.ClassicalSpectralSymmetry
import NLS.KdV.ClassicalDiscriminant
import NLS.KdV.ClassicalHillFlow
import NLS.KdV.HillClassicalIdentification
import NLS.FunctionalAnalysis.AbsoluteContinuityTranslation
import NLS.FunctionalAnalysis.LinearVolterraLinearity
import NLS.KdV.ClassicalHillMultipliers
import NLS.KdV.HillFullPeriod
import NLS.KdV.HillDiscriminantNecessity
import NLS.KdV.HillFirstOrderReduction
import NLS.KdV.HillL2SpectralCriterion
import NLS.KdV.HillDiscriminantComparison
import NLS.ComplexAnalysis.EntireEvenSquareDescent
import NLS.KdV.HillL2EnergyDiscriminant
import NLS.KdV.HillWeightIndependence
import NLS.KdV.HillPhysicalGapBounds
import NLS.Articles.KdVEstimates.EstimateAdapter
import Lean.Util.CollectAxioms

/-! Transitive audit of the shared KdV foundations and article adapters.
The article's main theorems are not claimed by this audit. -/

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let shared := #[``NLS.FiniteSpectralDeterminant.det_prod_formula,
    ``NLS.FiniteSpectralDeterminant.determinant_shift_bound,
    ``NLS.Weight.pullback, ``NLS.Weight.pullback_apply,
    ``NLS.WeightedCoeff.insertIsometry, ``NLS.WeightedCoeff.insertIsometry_image,
    ``NLS.WeightedCoeff.insertIsometry_outside, ``NLS.WeightedCoeff.norm_insertIsometry,
    ``NLS.Coeff.pair_sq_le_norm_sq, ``NLS.Coeff.positive_pair_tail_sq,
    ``NLS.ReciprocalSeries.summable_nat_reciprocal_sq_tail,
    ``NLS.ReciprocalSeries.tsum_nat_reciprocal_sq_tail_le,
    ``NLS.SpectralWeight.doubleIndex, ``NLS.SpectralWeight.doubleIndex_apply,
    ``NLS.FunctionalAnalysis.absolutelyContinuousOnInterval_comp_add_right,
    ``NLS.LinearVolterra.solution_add, ``NLS.LinearVolterra.solution_zero_initial,
    ``NLS.ComplexAnalysis.complex_sqrt_sq,
    ``NLS.ComplexAnalysis.analyticOnNhd_entire_even_square_descent]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`NLS.KdV).isPrefixOf name || (`NLS.Articles.KdVEstimates).isPrefixOf name ||
        shared.contains name then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      checked := checked + 1
  if checked == 0 then
    throwError "No candidate declarations were audited."
  logInfo m!"KdV foundation: transitive axiom audit passed for {checked} declarations."
