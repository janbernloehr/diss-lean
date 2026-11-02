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
import NLS.ComplexAnalysis.ZeroCountHomotopy
import NLS.ComplexAnalysis.TwoZeroOrderComparison
import NLS.KdV.ClassicalLocalPrimitive
import NLS.KdV.ClassicalFreePrimitive
import NLS.KdV.HillRealSpectrum
import NLS.KdV.HillCharacteristicZeros
import NLS.KdV.HillRealGapPairs
import NLS.KdV.HillWideLocalization
import NLS.ComplexAnalysis.RealDiameterDisc
import NLS.SequenceSpaces.OrderedOneSidedEnumeration
import NLS.KdV.HillFreeSpectrum
import NLS.KdV.HillCentralCounting
import NLS.KdV.HillCentralRoots
import NLS.KdV.HillGlobalRealLabels
import NLS.KdV.HillRealLabelingUniqueness
import NLS.KdV.HillCanonicalRealLabels
import NLS.KdV.HillCanonicalGapBounds
import NLS.SequenceSpaces.OrderedFiniteContinuity
import NLS.KdV.HillCumulativeCounts
import NLS.KdV.HillLabelContinuity
import NLS.KdV.HillCanonicalFreeLabels
import NLS.KdV.HillRealTraceParity
import NLS.ComplexAnalysis.TracePrimitiveContinuation
import NLS.KdV.HillL2SourcePrimitive
import NLS.KdV.HillL2HighContourMoments
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
    ``NLS.ComplexAnalysis.analyticOnNhd_entire_even_square_descent,
    ``NLS.ComplexAnalysis.isLocallyConstant_analyticZeroCount,
    ``NLS.ComplexAnalysis.analyticZeroCount_eq_of_homotopy,
    ``NLS.ComplexAnalysis.analyticOrderNatAt_eq_of_two_zero_counts,
    ``NLS.ComplexAnalysis.ofReal_mem_realDiameter_closedBall_iff,
    ``NLS.ComplexAnalysis.ofReal_mem_realDiameter_sphere_iff,
    ``NLS.ComplexAnalysis.ne_zero_on_realDiameter_sphere,
    ``NLS.appendPairedTail, ``NLS.appendPairedTail_prefix,
    ``NLS.appendPairedTail_even, ``NLS.appendPairedTail_odd,
    ``NLS.monotone_appendPairedTail,
    ``NLS.ComplexAnalysis.eventually_analyticZeroCount_eq_of_continuous_family,
    ``NLS.finiteLowerCount, ``NLS.finiteLowerCount_le_iff,
    ``NLS.index_lt_finiteLowerCount_iff, ``NLS.tendsto_ordered_finite_of_counts]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`NLS.KdV).isPrefixOf name || (`NLS.Articles.KdVEstimates).isPrefixOf name ||
        (`NLS.ComplexAnalysis.TracePrimitiveFamily).isPrefixOf name ||
        shared.contains name then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      checked := checked + 1
  if checked == 0 then
    throwError "No candidate declarations were audited."
  logInfo m!"KdV foundation: transitive axiom audit passed for {checked} declarations."
