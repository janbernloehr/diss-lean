import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Algebra.Group.Basic

/-! # Propagation of parameter continuity by continuous differences

On a connected spectral set, parameter continuity at one anchor
propagates to every point if nearby spectral values have a difference
that is continuous in the parameter. No global choice of local
additive constants is required.
-/
open Set Filter Topology
namespace NLS.ComplexAnalysis

/-- Locally continuous increments propagate parameter continuity
through a preconnected set from one known normalization point. -/
theorem continuousAt_parameter_of_local_differences
    {X A G : Type*} [TopologicalSpace X] [TopologicalSpace A]
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (F : X → A → G) (D : Set X) (b : A) (hD : IsPreconnected D)
    (hlocal : ∀ x ∈ D, ∀ᶠ y in 𝓝[D] x, ContinuousAt (fun a => F y a-F x a) b)
    (x : X) (hx : x ∈ D) (hanchor : ContinuousAt (F x) b) :
    ∀ y ∈ D, ContinuousAt (F y) b := by
  intro y hy
  have h := hD.induction₂ (fun u v => ContinuousAt (F u) b ↔ ContinuousAt (F v) b)
    (fun u hu => ?_) (fun _ _ _ _ _ _ huv hvw => huv.trans hvw)
    (fun _ _ _ _ huv => huv.symm) hx hy
  · exact h.mp hanchor
  · filter_upwards [hlocal u hu] with v hv
    constructor
    · intro hc
      simpa only [Pi.add_def,sub_add_cancel] using hv.add hc
    · intro hc
      simpa only [Pi.sub_def,sub_sub_cancel] using hc.sub hv

end NLS.ComplexAnalysis
