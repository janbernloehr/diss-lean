import NLS.Dynamics.ActionDependentWeightedPhaseFlow
import NLS.Articles.KdVKdV2Frequencies.SignedPhaseFlow
import NLS.Articles.KdVKdV2Frequencies.MassPhaseObstruction
import NLS.Articles.KdVKdV2Frequencies.SmoothKdVIdentities
import Lean.Util.CollectAxioms

/-! Transitive axiom audit of the candidate and its imported NLS dependencies.
This deliberately imports specific modules, not the aggregate NLS library.
-/

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`NLS.Dynamics.ActionDependentWeightedPhaseFlow,
    `NLS.Articles.KdVKdV2Frequencies.SignedPhaseFlow,
    `NLS.Articles.KdVKdV2Frequencies.MassPhaseObstruction,
    `NLS.Articles.KdVKdV2Frequencies.SmoothKdVIdentities]
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
