import NLS.Articles.MKdVNLSHierarchies.InitialChecks
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
    `NLS.ZakharovShabat.fderiv_sobolevNLSHamiltonian_reciprocal_scaling]
  let expected := #[``NLS.MKdV.diagonalNLSHamiltonian_even_eq_zero,
    ``NLS.MKdV.classicalNLSHamiltonian_three_diagonal,
    ``NLS.Articles.MKdVNLSHierarchies.theorem2_i_swap_covectors,
    ``NLS.Articles.MKdVNLSHierarchies.theorem2_i_phase_covectors]
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
