import NLS.Articles.MKdVNLSHierarchies.InitialChecks
import NLS.Articles.MKdVNLSHierarchies.SmoothFourthFlow
import NLS.MKdV.MiuraBoundaryTransfer
import NLS.Articles.MKdVNLSHierarchies.DiscriminantIdentity
import NLS.ZakharovShabat.ClassicalNLSHierarchyVariation
import NLS.Articles.MKdVNLSHierarchies.GradientSymmetries
import NLS.ZakharovShabat.NLSRiccatiResolvent
import NLS.DifferentialPolynomial.RiccatiResolventVariation
import NLS.Articles.MKdVNLSHierarchies.GradientRecurrence
import Lean.Util.CollectAxioms

/-! Audit every new public declaration and its generated auxiliary declarations.
The traversal includes all imported dependencies of each checked declaration. -/
open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let prefixes := #[`NLS.MKdV, `NLS.Articles.MKdVNLSHierarchies,
    `NLS.DifferentialPolynomial,
    `NLS.ZakharovShabat.nlsRiccatiPolynomial_eq_differentialRiccatiSequence,
    `NLS.ZakharovShabat.coeff_nls_differentialRiccatiSeries,
    `NLS.Fourier.circleUnitCoefficients,
    `NLS.Fourier.eq_of_periodic_integral_mul_eq,
    `NLS.Fourier.periodOneL2Distribution,
    `NLS.ZakharovShabat.nlsResolventCoefficientA,
    `NLS.ZakharovShabat.nlsResolventCoefficientB,
    `NLS.ZakharovShabat.backgroundEmbedding_nlsResolventA,
    `NLS.ZakharovShabat.backgroundEmbedding_nlsResolventB,
    `NLS.ZakharovShabat.exists_nlsResolvent_jet_variation,
    `NLS.ZakharovShabat.integral_firstVariationDensity_eq_resolvent,
    `NLS.ZakharovShabat.evaluate_euler_nlsRiccati_density_fst,
    `NLS.ZakharovShabat.evaluate_euler_nlsRiccati_density_snd,
    `NLS.ZakharovShabat.classicalNLSHierarchyGradient_eq_resolvent,
    `NLS.ZakharovShabat.topSobolevJetCircleL2,
    `NLS.ZakharovShabat.sobolevMonomialL2,
    `NLS.ZakharovShabat.analyticAt_sobolevMonomialL2,
    `NLS.ZakharovShabat.sobolevPolynomialL2,
    `NLS.ZakharovShabat.analyticAt_sobolevPolynomialL2,
    `NLS.ZakharovShabat.nlsHamiltonianPolynomial_derivativeOrder,
    `NLS.ZakharovShabat.nlsHierarchyEuler_derivativeOrder,
    `NLS.ZakharovShabat.nlsHamiltonianPolynomial_one,
    `NLS.ZakharovShabat.classicalNLSHierarchyGradient_one,
    `NLS.ZakharovShabat.sobolevNLSHierarchyGradient,
    `NLS.ZakharovShabat.analyticAt_sobolevNLSHierarchyGradient,
    `NLS.ZakharovShabat.hierarchyL2GradientCovector,
    `NLS.ZakharovShabat.fderiv_sobolevNLSHamiltonian_eq_gradient,
    `NLS.ZakharovShabat.sobolevNLSHierarchyVectorField,
    `NLS.FunctionalAnalysis.periodic_deriv,
    `NLS.FunctionalAnalysis.periodic_iteratedDeriv,
    `NLS.FunctionalAnalysis.contDiff_iteratedDeriv,
    `NLS.FunctionalAnalysis.integral_deriv_mul_periodic,
    `NLS.FunctionalAnalysis.integral_iteratedDeriv_mul_periodic,
    `NLS.LinearVolterra.unitIntervalMean,
    `NLS.LinearVolterra.unitIntervalMean_apply,
    `NLS.ZakharovShabat.nlsHamiltonianPolynomial,
    `NLS.ZakharovShabat.integral_evaluate_nlsHamiltonianPolynomial,
    `NLS.ZakharovShabat.classicalNLSHierarchyGradient,
    `NLS.ZakharovShabat.hasDerivAt_classicalNLSHamiltonian,
    `NLS.ZakharovShabat.contDiff_classicalNLSHierarchyGradient,
    `NLS.ZakharovShabat.periodic_classicalNLSHierarchyGradient,
    `NLS.ZakharovShabat.hierarchyComponentSwap,
    `NLS.ZakharovShabat.hierarchyComponentSwap_apply,
    `NLS.ZakharovShabat.sobolevNLSHamiltonian_neg,
    `NLS.ZakharovShabat.sobolevNLSHamiltonian_swap,
    `NLS.ZakharovShabat.fderiv_sobolevNLSHamiltonian_swap,
    `NLS.ZakharovShabat.hierarchyReciprocalScaling,
    `NLS.ZakharovShabat.hierarchyReciprocalScaling_apply,
    `NLS.ZakharovShabat.fderiv_sobolevNLSHamiltonian_reciprocal_scaling,
    `NLS.ZakharovShabat.nlsRiccatiDensity_three,
    `NLS.ZakharovShabat.classicalNLSHamiltonian_four,
    `NLS.ZakharovShabat.classicalNLSHamiltonian_four_swap,
    `NLS.ZakharovShabat.classicalNLSHamiltonian_four_variation_fst,
    `NLS.ZakharovShabat.hasDerivAt_classicalNLSHamiltonian_four_fst,
    `NLS.ZakharovShabat.hasDerivAt_classicalNLSHamiltonian_four_snd,
    `NLS.ZakharovShabat.classicalNLSFourthGradient,
    `NLS.ZakharovShabat.solutionMap_classicalCoefficientCurve,
    `NLS.ZakharovShabat.classicalDiscriminant_eq_flowTrace,
    `NLS.LinearVolterra.absolutelyContinuous_solution,
    `NLS.LinearVolterra.solutionMap,
    `NLS.LinearVolterra.solutionMap_apply,
    `NLS.LinearVolterra.solutionMap_intertwine,
    `NLS.LinearVolterra.trace_solutionMap_intertwine,
    `NLS.LinearVolterra.trace_pairCLM]
  let expected := #[``NLS.MKdV.diagonalNLSHamiltonian_even_eq_zero,
    ``NLS.DifferentialPolynomial.hasDerivAt_integral_evaluate_euler,
    ``NLS.ZakharovShabat.hasDerivAt_classicalNLSHamiltonian,
    ``NLS.ZakharovShabat.fderiv_sobolevNLSHamiltonian_eq_gradient,
    ``NLS.DifferentialPolynomial.constructed_riccati_resolvent_identities,
    ``NLS.DifferentialPolynomial.riccati_resolvent_coefficient_variation,
    ``NLS.DifferentialPolynomial.coeff_riccatiResolventCoupling_even_diagonal,
    ``NLS.ZakharovShabat.coeff_nls_differentialRiccatiSeries,
    ``NLS.Articles.MKdVNLSHierarchies.theorem2_i_swap_gradients,
    ``NLS.Articles.MKdVNLSHierarchies.theorem2_i_phase_gradients,
    ``NLS.Articles.MKdVNLSHierarchies.theorem2_i_phase_vector_fields,
    ``NLS.Articles.MKdVNLSHierarchies.theorem2_i_swap_vector_fields,
    ``NLS.Articles.MKdVNLSHierarchies.theorem2_ii_corrected,
    ``NLS.Articles.MKdVNLSHierarchies.theorem2_ii_corrected_coefficients,
    ``NLS.ZakharovShabat.classicalNLSHierarchyGradient_eq_resolvent,
    ``NLS.MKdV.classicalNLSHamiltonian_three_diagonal,
    ``NLS.Articles.MKdVNLSHierarchies.theorem2_i_swap_covectors,
    ``NLS.Articles.MKdVNLSHierarchies.theorem2_i_phase_covectors,
    ``NLS.Articles.MKdVNLSHierarchies.theorem1_m2_smooth,
    ``NLS.MKdV.hasDerivAt_classicalMKdVEnergy,
    ``NLS.ZakharovShabat.hasDerivAt_classicalNLSHamiltonian_four_fst,
    ``NLS.ZakharovShabat.hasDerivAt_classicalNLSHamiltonian_four_snd,
    ``NLS.MKdV.miura_equation_classicalSolution,
    ``NLS.MKdV.miura_floquet_condition_iff,
    ``NLS.Articles.MKdVNLSHierarchies.theorem5_discriminant_identity,
    ``NLS.Articles.MKdVNLSHierarchies.hill_column_spec,
    ``NLS.MKdV.physicalMiuraSolution_unique,
    ``NLS.MKdV.quasiHillDiscriminant_eq_ZS,
    ``NLS.LinearVolterra.trace_solutionMap_intertwine]
  let env ← getEnv
  for name in expected do
    unless (env.find? name).isSome do
      throwError "Missing required checked declaration {name}"
  let mut checked : Nat := 0
  for (name, _) in env.constants do
    if prefixes.any (fun scopeName => scopeName.isPrefixOf name) then
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do
          throwError "{name} depends transitively on disallowed axiom {ax}"
      checked := checked + 1
  if checked == 0 then
    throwError "The article axiom audit did not run."
  logInfo m!"mKdV/NLS article axiom audit passed for {checked} declarations (including auxiliaries)."
