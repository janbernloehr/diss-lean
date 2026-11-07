import NLS.Dynamics.ConjugatedContinuousEvolution
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! # Recovering an evolution equation from dense classical trajectories

A continuous complete-trajectory map and a continuous vector field
transport convergence of initial data to locally uniform convergence of
both trajectories and their derivatives. The differential equation then
passes to the limit in the actual Banach target norm.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.Dynamics
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivAt_of_continuous_evolution_approximation
    (T : C(E,C(ℝ,E))) (L : E →L[ℝ] F) (V : C(E,F))
    (q : E) (a : ℕ → E) (ha : Tendsto a atTop (𝓝 q))
    (hd : ∀ N t, HasDerivAt (fun u : ℝ => L (T (a N) u)) (V (T (a N) t)) t)
    (t : ℝ) : HasDerivAt (fun u : ℝ => L (T q u)) (V (T q t)) t := by
  have hT := T.continuous.continuousAt.tendsto.comp ha
  have hV := (ContinuousMap.continuous_postcomp V).continuousAt.tendsto.comp hT
  have hL := (ContinuousMap.continuous_postcomp (⟨L,L.continuous⟩ : C(E,F))).continuousAt.tendsto.comp hT
  have hVu := (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hV).tendstoLocallyUniformlyOn (s := Set.univ)
  have hLu := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hL
  exact hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hVu
    (Filter.Eventually.of_forall (fun N t _ => hd N t))
    (fun u _ => (hLu.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ u)) (Set.mem_univ t)

end NLS.Dynamics
