import NLS.Articles.DNLSEstimates.MainEstimates
import NLS.Articles.DNLSEstimates.Hierarchy
import NLS.Articles.DNLSEstimates.HigherActions
import NLS.Articles.DNLSEstimates.SpectralEstimates
import NLS.Articles.DNLSEstimates.ActionEstimates
import NLS.Articles.DNLSEstimates.Primitive
import NLS.Articles.DNLSEstimates.ComplexActions
import NLS.Articles.DNLSEstimates.ConverseEstimate
import NLS.Articles.DNLSEstimates.FiniteGap
import NLS.Articles.DNLSEstimates.ComplexFiniteGap
import NLS.Articles.DNLSEstimates.SpectralCurve
import NLS.Articles.DNLSEstimates.SpectralSurface
import NLS.Articles.DNLSEstimates.NonsmoothHamiltonians
import NLS.Articles.DNLSEstimates.SpectralConnectedness
import NLS.Articles.DNLSEstimates.SpectralNodes
import NLS.Articles.DNLSEstimates.RootDomains
import NLS.Articles.DNLSEstimates.Gevrey
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`NLS.Articles.DNLSEstimates).isPrefixOf name then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      logInfo m!"{name}: {axioms}"
      checked := checked + 1
  if checked == 0 then
    throwError "No article declarations were found."
  logInfo m!"Transitive axiom audit passed for {checked} article declarations."

#print axioms NLS.ZakharovShabat.sourceSection23_original_estimates
#print axioms NLS.ZakharovShabat.SourceSection17OriginalData.section23_sobolev_bounds
#print axioms NLS.ZakharovShabat.SourceSection20Data.section23_weighted_neighborhood
#print axioms NLS.ZakharovShabat.SourceSection20Data.section23_realSobolev_neighborhood
