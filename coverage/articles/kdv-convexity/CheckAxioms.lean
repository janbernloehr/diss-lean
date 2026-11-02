import NLS.KdV.ClassicalTraceAsymptotics
import NLS.KdV.ClassicalBranchPrimitive
import NLS.KdV.ClassicalContourMoments
import NLS.KdV.ClassicalHighGapFamilies
import NLS.KdV.ClassicalHillMomentReality
import NLS.KdV.ClassicalHillHighEndpointNormalization
import NLS.KdV.ClassicalHillSquaredPrimitiveMatching
import NLS.KdV.ClassicalHillWholeGapSquares
import NLS.KdV.ClassicalHillGapCutRoots
import NLS.KdV.ActionHamiltonianFiniteGap
import NLS.Articles.KdVConvexity.LocalConsequences
import NLS.Articles.KdVConvexity.BaseContourSeries
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let namespaces := #[`NLS.Articles.KdVConvexity, `NLS.KdV]
  let additional := #[``NLS.ZakharovShabat.norm_continuousPotentialL2Class_le_two_norm,
    ``NLS.ZakharovShabat.continuousPotentialL2CLM,
    ``NLS.ZakharovShabat.continuousPotentialL2CLM_apply,
    ``NLS.ZakharovShabat.classicalSolution_injective_initial,
    ``NLS.ZakharovShabat.classicalSolution_eq_zero_imp_initial_eq_zero,
    ``NLS.ComplexAnalysis.twoZeroQuotient,
    ``NLS.ComplexAnalysis.dslope_zero_at_second_zero,
    ``NLS.ComplexAnalysis.twoZeroQuotient_factor,
    ``NLS.ComplexAnalysis.analyticOnNhd_twoZeroQuotient,
    ``NLS.ComplexAnalysis.twoZeroQuotient_ne_zero,
    ``NLS.ComplexAnalysis.norm_twoZeroQuotient_le,
    ``NLS.ComplexAnalysis.analyticOnNhd_continuous_squareRoot,
    ``NLS.ComplexAnalysis.exists_analytic_squareRoot_on_ball,
    ``NLS.ComplexAnalysis.endpointRoot,
    ``NLS.ComplexAnalysis.midpoint_mem_complex_segment,
    ``NLS.ComplexAnalysis.endpointRoot_sq,
    ``NLS.ComplexAnalysis.analyticOnNhd_endpointRoot,
    ``NLS.ComplexAnalysis.exists_analytic_squareRoot_on_two_zero_cut]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if namespaces.any (fun ns => ns.isPrefixOf name) || additional.contains name then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      logInfo m!"{name}: {axioms}"
      checked := checked + 1
  if checked == 0 then
    throwError "No article or shared KdV declarations found"
  logInfo m!"Transitive axiom audit passed for {checked} article/shared KdV declarations."
