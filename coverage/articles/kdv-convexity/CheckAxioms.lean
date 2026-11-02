import NLS.KdV.ClassicalTraceAsymptotics
import NLS.KdV.ActionHamiltonianFiniteGap
import NLS.Articles.KdVConvexity.LocalConsequences
import NLS.Articles.KdVConvexity.BaseContourSeries
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let namespaces := #[`NLS.Articles.KdVConvexity, `NLS.KdV]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if namespaces.any (fun ns => ns.isPrefixOf name) then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      logInfo m!"{name}: {axioms}"
      checked := checked + 1
  if checked == 0 then
    throwError "No article or shared KdV declarations found"
  logInfo m!"Transitive axiom audit passed for {checked} article/shared KdV declarations."
