import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Extending a time equation from a dense parameter set

Joint continuity of the paths and velocities gives locally uniform velocity
convergence. A derivative identity on a dense set of initial parameters then
extends to every parameter. The proof uses the neighborhood filter directly.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.FunctionalAnalysis

/-- A continuously parameterized time equation valid on a dense set of
parameters holds everywhere, with no differentiability in the parameter. -/
theorem hasDerivAt_of_dense_parameters
    {E Y : Type*} [TopologicalSpace E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (S : Set E) (hS : Dense S) (u v : E → ℝ → Y)
    (hu : Continuous (fun x : E × ℝ => u x.1 x.2))
    (hv : Continuous (fun x : E × ℝ => v x.1 x.2))
    (hd : ∀ a ∈ S, ∀ t : ℝ, HasDerivAt (u a) (v a t) t)
    (a : E) (t : ℝ) : HasDerivAt (u a) (v a t) t := by
  let l := 𝓝[S] a
  have : NeBot l := mem_closure_iff_nhdsWithin_neBot.mp (hS a)
  let V : E → C(ℝ,Y) := fun b => ⟨v b,hv.comp (continuous_const.prodMk continuous_id)⟩
  have hV : Continuous V := ContinuousMap.continuous_of_continuous_uncurry V hv
  have hlim : Tendsto V l (𝓝 (V a)) := hV.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hloc := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim
  apply hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
    (hloc.tendstoLocallyUniformlyOn (s := univ))
  · filter_upwards [self_mem_nhdsWithin] with b hb
    intro r _
    exact hd b hb r
  · intro r _
    exact (hu.comp (continuous_id.prodMk continuous_const)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · trivial

end NLS.FunctionalAnalysis
