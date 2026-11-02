import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.SequenceSpaces.PeriodOneMiuraCharts
import NLS.SequenceSpaces.PeriodOneMiuraRegularity
import NLS.KdV.ClassicalTraceAsymptotics
import NLS.KdV.ClassicalBranchPrimitive
import NLS.KdV.ClassicalContourMoments
import NLS.KdV.ClassicalHighGapFamilies
import NLS.KdV.ClassicalHillMomentReality
import NLS.KdV.ClassicalHillHighEndpointNormalization
import NLS.KdV.ClassicalHillSquaredPrimitiveMatching
import NLS.KdV.ClassicalHillWholeGapSquares
import NLS.KdV.ClassicalHillGapCutRoots
import NLS.KdV.ClassicalHillCubicGapBounds
import NLS.KdV.ClassicalL2PrimitiveAgreement
import NLS.KdV.ClassicalL2ContourAgreement
import NLS.KdV.HillL2DiscAsymptotics
import NLS.KdV.HillL2GapSquareFamilies
import NLS.KdV.HillL2HighMomentFamilies
import NLS.KdV.HillL2ArnoldActionComparison
import NLS.KdV.ClassicalHillGapQuotientAsymptotics
import NLS.KdV.ClassicalHillArnoldActionComparison
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
    ``NLS.ComplexAnalysis.norm_two_root_quotient_sub_le_on_disc,
    ``NLS.ComplexAnalysis.analyticOnNhd_continuous_squareRoot,
    ``NLS.ComplexAnalysis.exists_analytic_squareRoot_on_ball,
    ``NLS.ComplexAnalysis.endpointRoot,
    ``NLS.ComplexAnalysis.midpoint_mem_complex_segment,
    ``NLS.ComplexAnalysis.endpointRoot_sq,
    ``NLS.ComplexAnalysis.analyticOnNhd_endpointRoot,
    ``NLS.ComplexAnalysis.exists_analytic_squareRoot_on_two_zero_cut,
    ``NLS.ComplexAnalysis.norm_sq_sub_sq_of_small_sphere,
    ``NLS.ComplexAnalysis.square_circleMap_sub_linear,
    ``NLS.ComplexAnalysis.squaredCirclePath_contDiffOn,
    ``NLS.ComplexAnalysis.squaredCircleHomotopy_annulus,
    ``NLS.ComplexAnalysis.circleIntegral_square_pullback_eq_energy_circle,
    ``NLS.ComplexAnalysis.circleIntegral_eq_of_analytic_cut_nestedCircles]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let additionalModules := #[`NLS.ComplexAnalysis.AnalyticUnitDerivativeInverse,
    `NLS.ComplexAnalysis.AnalyticOpenInverse,
    `NLS.ComplexAnalysis.SmallQuadraticInverse,
    `NLS.SequenceSpaces.PeriodOneMassResolvent,
    `NLS.SequenceSpaces.PeriodOneMiuraQuadratic,
    `NLS.SequenceSpaces.PeriodOneMiuraCharts,
    `NLS.SequenceSpaces.PeriodOneMiuraRegularity,
    `NLS.SequenceSpaces.PeriodOneMiuraShift,
    `NLS.ComplexAnalysis.EntireEvenSquareDescent,
    `NLS.ComplexAnalysis.AnalyticLocalLipschitz,
    `NLS.ComplexAnalysis.NormalizedSquareRootBounds,
    `NLS.ComplexAnalysis.LogarithmStripNormalization,
    `NLS.ComplexAnalysis.QuadraticRootContourPeriod,
    `NLS.ComplexAnalysis.TracePrimitiveContinuation,
    `NLS.ComplexAnalysis.TracePrimitiveMoments,
    `NLS.ComplexAnalysis.TracePrimitiveFunctoriality,
    `NLS.ComplexAnalysis.TwoZeroOrderComparison,
    `NLS.ComplexAnalysis.ZeroCountHomotopy,
    `NLS.FunctionalAnalysis.AbsoluteContinuityTranslation,
    `NLS.FunctionalAnalysis.LinearVolterraLinearity,
    `NLS.FunctionalAnalysis.TwoDimensionalDeterminant,
    `NLS.SequenceSpaces.WeightedInsertion]
  let mut checked : Nat := 0
  let env ← getEnv
  for (name, _) in env.constants do
    let fromSharedModule := (env.getModuleIdxFor? name).any
      (fun idx => additionalModules.contains env.header.moduleNames[idx.toNat]!)
    if namespaces.any (fun ns => ns.isPrefixOf name) || additional.contains name || fromSharedModule then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      logInfo m!"{name}: {axioms}"
      checked := checked + 1
  if checked == 0 then
    throwError "No article or shared KdV declarations found"
  logInfo m!"Transitive axiom audit passed for {checked} article/shared KdV declarations."
