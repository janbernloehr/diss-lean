import NLS
import Lean.Util.CollectAxioms

/-!
Audit every declaration in the `NLS` namespace, including definitions and
instances. Only Lean's usual classical axioms are allowed transitively.
An admitted proof (`sorryAx`) or a new project axiom makes this command fail.
-/

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`NLS).isPrefixOf name then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      checked := checked + 1
  if checked == 0 then
    throwError "No NLS declarations were found; the audit did not run."
  logInfo m!"Axiom audit passed for {checked} NLS declarations."
