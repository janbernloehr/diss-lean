import NLS.ComplexAnalysis.PrimitiveRemovableBoundary

/-! # Boundary limits survive continuous extension to a domain's closure

A bound near a boundary point extends to closure points by continuity.
This transfers a half-plane limit onto a real interval where a primitive
has been continued analytically, without choosing an approach rate.
-/
noncomputable section
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis

/-- An extension agreeing on an open chart retains a relative boundary
limit along the part of that chart in the original domain's closure. -/
theorem tendsto_continuous_extension_on_closure
    (F E : ℂ → ℂ) (Ω D : Set ℂ) (c A : ℂ)
    (hD : IsOpen D) (hE : ContinuousOn E D) (hmatch : EqOn E F (D ∩ Ω))
    (hF : Tendsto F (𝓝[Ω] c) (𝓝 A)) :
    Tendsto E (𝓝[D ∩ closure Ω] c) (𝓝 A) := by
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := Metric.tendsto_nhdsWithin_nhds.mp hF (ε/2) (half_pos hε)
  refine ⟨δ,hδ,?_⟩
  intro z hz hnear
  let U := D ∩ ball c δ
  have hU : IsOpen U := hD.inter isOpen_ball
  have hzU : z ∈ U := ⟨hz.1,hnear⟩
  let : NeBot (𝓝[U ∩ Ω] z) := by
    rw [nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (hU.mem_nhds hzU))]
    exact mem_closure_iff_nhdsWithin_neBot.mp hz.2
  have hc : ContinuousAt (fun w => dist (E w) A) z :=
    (hE.continuousAt (hD.mem_nhds hz.1)).dist continuousAt_const
  have hlim : Tendsto (fun w => dist (E w) A) (𝓝[U ∩ Ω] z) (𝓝 (dist (E z) A)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have hle : dist (E z) A ≤ ε/2 := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hmatch ⟨hw.1.1,hw.2⟩]
    exact (hbound hw.2 hw.1.2).le
  exact hle.trans_lt (half_lt_self hε)

end NLS.ComplexAnalysis
