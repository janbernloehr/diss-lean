import NLS.Articles.MKdVNLSHierarchies.InitialChecks
import NLS.Articles.MKdVNLSHierarchies.SmoothFourthFlow
import NLS.MKdV.MiuraBoundaryTransfer
import NLS.Articles.MKdVNLSHierarchies.DiscriminantIdentity
import Lean.Util.CollectAxioms

/-! Audit every new public declaration and its generated auxiliary declarations.
The traversal includes all imported dependencies of each checked declaration. -/
open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let prefixes := #[`NLS.MKdV, `NLS.Articles.MKdVNLSHierarchies,
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
