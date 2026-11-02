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
import NLS.ComplexAnalysis.TracePrimitiveMoments
import NLS.KdV.HillL2ContourDeformation
import NLS.Fourier.ContinuousConjugation
import NLS.KdV.ClassicalHillConjugation
import NLS.KdV.HillL2Conjugation
import NLS.ComplexAnalysis.TracePrimitiveReflection
import NLS.KdV.HillL2PrimitiveReflection
import NLS.KdV.HillRealBands
import NLS.ComplexAnalysis.RealSimpleZeroSigns
import NLS.KdV.HillRealGapSigns
import NLS.KdV.HillRealGapIntegrals
import NLS.ComplexAnalysis.AnalyticDiscSquareRoot
import NLS.ComplexAnalysis.AnalyticTwoZeroRoot
import NLS.ComplexAnalysis.TwoZeroDeflation
import NLS.ComplexAnalysis.TwoZeroRootEndpointBound
import NLS.KdV.HillL2GapCutRoots
import NLS.KdV.HillL2GapCutPrimitives
import NLS.KdV.HillL2GapCutBoundary
import NLS.KdV.HillL2CollapsedGapMoments
import NLS.ComplexAnalysis.TraceRootPrimitive
import NLS.KdV.HillL2NormalizedCutPrimitive
import NLS.KdV.HillL2CutPrimitiveReflection
import NLS.KdV.HillL2CutPrimitiveEndpointValues
import NLS.ComplexAnalysis.LogarithmStripNormalization
import NLS.KdV.HillL2RealSourcePhase
import NLS.KdV.HillL2CutRealPhase
import NLS.KdV.HillL2CutEndpointNormalization
import NLS.ComplexAnalysis.RealCutConjugation
import NLS.ComplexAnalysis.GapPrimitiveSquare
import NLS.ComplexAnalysis.CoshSquareCoordinate
import NLS.KdV.HillL2CutPrimitiveSquare
import NLS.KdV.HillL2CutSquareTrace
import NLS.KdV.HillL2CutSquareDeflation
import NLS.ComplexAnalysis.RealTwoZeroUnit
import NLS.ComplexAnalysis.RealEndpointRootBoundary
import NLS.KdV.HillL2CutPrimitiveUnit
import NLS.KdV.HillL2CutUnitOrientation
import NLS.KdV.HillL2GapBoundaryValues
import NLS.Articles.KdVEstimates.EstimateAdapter
import NLS.ComplexAnalysis.RealGapEllipse
import NLS.ComplexAnalysis.RealGapEllipseHomotopy
import NLS.ComplexAnalysis.RealGapEllipseIntegral
import NLS.ComplexAnalysis.RealGapEllipseLimit
import NLS.ComplexAnalysis.RealCutCircleIntegral
import NLS.ComplexAnalysis.NestedCircleHomotopy
import NLS.ComplexAnalysis.AnalyticCutContour
import NLS.KdV.HillL2GapContourIntegral
import NLS.KdV.HillL2HighGapMoments
import NLS.KdV.HillL2DiscAsymptotics
import NLS.ZakharovShabat.ContinuousPotentialL2Bound
import NLS.KdV.ClassicalSpectralEmbedding
import NLS.KdV.ClassicalHillSpectrum
import NLS.KdV.ClassicalSourcePrimitive
import NLS.KdV.ClassicalContourCoverage
import NLS.KdV.ClassicalHillDiscAsymptotics
import NLS.KdV.ClassicalHillHighTracePhase
import NLS.KdV.HillL2TraceControl
import NLS.ZakharovShabat.ClassicalSolutionInjectivity
import NLS.KdV.ClassicalHillGreen
import NLS.KdV.ClassicalHighGapPairs
import NLS.KdV.ClassicalHillReality
import NLS.KdV.ClassicalHillPrimitiveSheets
import NLS.KdV.ClassicalHillPrimitiveReflection
import NLS.KdV.ClassicalHillBandNormalization
import NLS.KdV.ClassicalHillHighPrimitiveStrip
import NLS.KdV.HillL2PrimitiveStrip
import NLS.KdV.ClassicalBranchPrimitive
import NLS.KdV.ClassicalCoshStripControl
import NLS.KdV.ClassicalHillSmallDiscTrace
import NLS.KdV.ClassicalHillSmallGapCoverage
import NLS.KdV.ClassicalHillHighEndpointNormalization
import NLS.KdV.ClassicalHillSquaredPrimitiveMatching
import NLS.KdV.ClassicalHillWholeGapSquares
import NLS.KdV.HillL2WholeGapSquares
import NLS.ComplexAnalysis.AnalyticLocalLipschitz
import NLS.KdV.ClassicalHillFreeSquareComparison
import NLS.KdV.HillL2FreeSquareComparison
import NLS.KdV.HillL2HighGapPairs
import NLS.KdV.HillL2SmallGapCoverage
import NLS.KdV.HillL2GapSquareFamilies
import NLS.KdV.HillL2GapQuotients
import NLS.ComplexAnalysis.NormalizedSquareRootBounds
import NLS.KdV.HillL2GapQuotientAsymptotics
import NLS.KdV.HillHighMomentComparison
import NLS.KdV.HillL2GapSquareIdentification
import NLS.KdV.HillRealGapUnitBound
import NLS.KdV.HillEventualActionGapBound
import NLS.KdV.HillWeightedRealActions
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
    ``NLS.index_lt_finiteLowerCount_iff, ``NLS.tendsto_ordered_finite_of_counts,
    ``NLS.Fourier.continuousFourierCLM_star,
    ``NLS.ComplexAnalysis.circleIntegral_pow_mul_deriv_eq_neg,
    ``NLS.ComplexAnalysis.circleIntegral_eq_conj_of_anti_conj,
    ``NLS.ComplexAnalysis.circleIntegral_im_eq_zero_of_anti_conj,
    ``NLS.ComplexAnalysis.not_isLocalExtr_of_simple_real_zero,
    ``NLS.ComplexAnalysis.negative_on_preconnected_of_nonzero,
    ``NLS.ComplexAnalysis.positive_right_of_negative_left,
    ``NLS.ComplexAnalysis.positive_left_of_negative_right,
    ``NLS.ComplexAnalysis.above_pos_level_of_square_gt,
    ``NLS.ComplexAnalysis.above_pos_level_of_square_gt_left,
    ``NLS.ComplexAnalysis.analyticOnNhd_continuous_squareRoot,
    ``NLS.ComplexAnalysis.exists_analytic_squareRoot_on_ball,
    ``NLS.ComplexAnalysis.endpointRoot,
    ``NLS.ComplexAnalysis.midpoint_mem_complex_segment,
    ``NLS.ComplexAnalysis.endpointRoot_sq,
    ``NLS.ComplexAnalysis.analyticOnNhd_endpointRoot,
    ``NLS.ComplexAnalysis.exists_analytic_squareRoot_on_two_zero_cut,
    ``NLS.ComplexAnalysis.twoZeroQuotient,
    ``NLS.ComplexAnalysis.dslope_zero_at_second_zero,
    ``NLS.ComplexAnalysis.twoZeroQuotient_factor,
    ``NLS.ComplexAnalysis.analyticOnNhd_twoZeroQuotient,
    ``NLS.ComplexAnalysis.twoZeroQuotient_ne_zero,
    ``NLS.ComplexAnalysis.norm_twoZeroQuotient_le,
    ``NLS.ComplexAnalysis.exists_two_zero_root_endpoint_bound,
    ``NLS.ComplexAnalysis.exists_primitive_on_disc_complement_of_zero_period,
    ``NLS.ComplexAnalysis.exists_primitive_segment_left_boundary_limit,
    ``NLS.ComplexAnalysis.exists_primitive_segment_right_boundary_limit,
    ``NLS.ComplexAnalysis.hasDerivAt_traceRoot_multiplier,
    ``NLS.ComplexAnalysis.exp_primitive_of_traceRoot,
    ``NLS.ComplexAnalysis.exp_neg_primitive_of_traceRoot,
    ``NLS.ComplexAnalysis.traceRoot_identities_of_exp,
    ``NLS.ComplexAnalysis.traceRoot_primitive_reflection,
    ``NLS.ComplexAnalysis.traceRoot_primitive_boundary_values,
    ``NLS.ComplexAnalysis.multiplier_eq_exp_of_normalized_primitive,
    ``NLS.ComplexAnalysis.real_mem_Ioo_of_preconnected_avoids,
    ``NLS.ComplexAnalysis.sinh_eq_zero_of_re_zero_im_int_pi,
    ``NLS.ComplexAnalysis.exp_neg_I_nat_pi,
    ``NLS.ComplexAnalysis.eq_zero_of_exp_eq_one_of_abs_im_le_pi,
    ``NLS.ComplexAnalysis.eq_of_exp_eq_of_abs_im_sub_le_pi,
    ``NLS.ComplexAnalysis.conj_mem_real_cut,
    ``NLS.ComplexAnalysis.gapPrimitiveSquareExtension,
    ``NLS.ComplexAnalysis.gapPrimitiveSquareExtension_spec,
    ``NLS.ComplexAnalysis.coshSquareCoordinate,
    ``NLS.ComplexAnalysis.coshSquareCoordinate_sq,
    ``NLS.ComplexAnalysis.analyticOnNhd_coshSquareCoordinate,
    ``NLS.ComplexAnalysis.coshSquareCoordinate_ofReal,
    ``NLS.ComplexAnalysis.coshSquareCoordinate_neg_ofReal,
    ``NLS.ComplexAnalysis.coshSquareCoordinate_re_le_one_of_nonpos,
    ``NLS.ComplexAnalysis.cosh_add_I_nat_pi,
    ``NLS.ComplexAnalysis.deriv_coshSquareCoordinate_zero,
    ``NLS.ComplexAnalysis.deriv_ne_zero_of_analyticOrderNatAt_eq_one,
    ``NLS.ComplexAnalysis.im_eq_zero_of_mem_real_segment,
    ``NLS.ComplexAnalysis.not_mem_real_segment_of_im_ne_zero,
    ``NLS.ComplexAnalysis.real_two_zero_unit_conj,
    ``NLS.ComplexAnalysis.endpointRoot_real_gap_limits,
    ``NLS.ZakharovShabat.normalizedStandardRoot_re_neg_of_gt_rightEndpoint,
    ``NLS.ZakharovShabat.normalizedStandardRoot_tendsto_gap_upper_side,
    ``NLS.ZakharovShabat.normalizedStandardRoot_tendsto_gap_lower_side,
    ``NLS.ComplexAnalysis.realGapEllipse,
    ``NLS.ComplexAnalysis.realGapEllipse_re,
    ``NLS.ComplexAnalysis.realGapEllipse_im,
    ``NLS.ComplexAnalysis.realGapEllipse_zero,
    ``NLS.ComplexAnalysis.realGapEllipse_two_pi,
    ``NLS.ComplexAnalysis.hasDerivAt_realGapEllipse,
    ``NLS.ComplexAnalysis.realGapEllipse_mem_closedBall,
    ``NLS.ComplexAnalysis.re_mem_Icc_of_mem_real_segment,
    ``NLS.ComplexAnalysis.realGapEllipse_not_mem_segment,
    ``NLS.ComplexAnalysis.tendsto_realGapEllipse,
    ``NLS.ComplexAnalysis.realGapEllipsePath,
    ``NLS.ComplexAnalysis.realGapEllipsePath_contDiffOn,
    ``NLS.ComplexAnalysis.circlePath_symm_apply,
    ``NLS.ComplexAnalysis.circlePath_symm_contDiffOn,
    ``NLS.ComplexAnalysis.realGapEllipse_affine_coordinates,
    ``NLS.ComplexAnalysis.realGapEllipse_affine_mem_closedBall,
    ``NLS.ComplexAnalysis.realGapEllipse_affine_not_mem_segment,
    ``NLS.ComplexAnalysis.curveIntegral_realGapEllipse_eq_neg_circleIntegral,
    ``NLS.ComplexAnalysis.curveIntegral_realGapEllipse_eq_intervalIntegral,
    ``NLS.ComplexAnalysis.realGapEllipse_limit_mem_Icc,
    ``NLS.ComplexAnalysis.tendsto_realGapEllipse_lower,
    ``NLS.ComplexAnalysis.tendsto_realGapEllipse_upper,
    ``NLS.ComplexAnalysis.tendsto_deriv_realGapEllipse,
    ``NLS.ComplexAnalysis.norm_deriv_realGapEllipse_le,
    ``NLS.ComplexAnalysis.tendsto_realGapEllipse_intervalIntegral,
    ``NLS.ComplexAnalysis.integral_real_cosine_pullback,
    ``NLS.ComplexAnalysis.tendsto_curveIntegral_realGapEllipse,
    ``NLS.ComplexAnalysis.exists_norm_bound_of_continuous_square_on_compact,
    ``NLS.ComplexAnalysis.circleIntegral_eq_neg_real_cut_jump,
    ``NLS.ComplexAnalysis.lineMap_circleMap_centers_radii,
    ``NLS.ComplexAnalysis.affineCircleHomotopy_ne_of_mem_both_balls,
    ``NLS.ComplexAnalysis.affineCircleHomotopy_mem_outer_closedBall,
    ``NLS.ComplexAnalysis.circleIntegral_eq_of_analytic_cut_nestedCircles,
    ``NLS.ComplexAnalysis.norm_two_root_quotient_sub_le_on_disc,
    ``NLS.ZakharovShabat.norm_continuousPotentialL2Class_le_two_norm,
    ``NLS.ZakharovShabat.continuousPotentialL2CLM,
    ``NLS.ZakharovShabat.continuousPotentialL2CLM_apply,
    ``NLS.ZakharovShabat.classicalSolution_injective_initial,
    ``NLS.ZakharovShabat.classicalSolution_eq_zero_imp_initial_eq_zero,
    ``NLS.ComplexAnalysis.exists_local_lipschitz_bound_of_analyticAt,
    ``NLS.ComplexAnalysis.norm_sqrt_sub_one_le,
    ``NLS.ComplexAnalysis.prescribedSquareRoot_analytic_and_close]
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
