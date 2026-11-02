import NLS.KdV.FreeHill
import NLS.Articles.KdVEstimates.EstimateAdapter
import Lean.Util.CollectAxioms

/-! Transitive audit of all declarations introduced by this private candidate.
The article's main theorems are not claimed by this audit. -/

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`NLS.KdV).isPrefixOf name || (`NLS.Articles.KdVEstimates).isPrefixOf name then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      checked := checked + 1
  if checked == 0 then
    throwError "No candidate declarations were audited."
  logInfo m!"Private KdV candidate: transitive axiom audit passed for {checked} declarations."
