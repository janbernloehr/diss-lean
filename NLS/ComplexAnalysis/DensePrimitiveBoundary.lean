import NLS.ComplexAnalysis.DensePrimitiveGluing

/-!
# Boundary normalization after gluing across a dense cut complement

If a continuous extension has the same norm as an endpoint-normalized
exterior function away from a cut, that exterior limit fixes its boundary
value even for approaches along the cut. Bounds extend by density.
-/

noncomputable section
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis

theorem tendsto_zero_of_dense_exterior_norm
    (F E : ℂ → ℂ) (Ω D K : Set ℂ) (c A : ℂ)
    (hD : IsOpen D) (hDense : Dense Kᶜ) (hDΩ : D ⊆ Ω)
    (hE : ContinuousOn E D)
    (hmatch : ∀ z ∈ D \ K, ‖E z‖ = ‖F z-A‖)
    (hF : Tendsto F (𝓝[Ω \ K] c) (𝓝 A)) :
    Tendsto E (𝓝[D] c) (𝓝 0) := by
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := Metric.tendsto_nhdsWithin_nhds.mp hF (ε/2) (half_pos hε)
  refine ⟨δ,hδ,?_⟩
  intro z hz hnear
  let U := D ∩ ball c δ
  have hU : IsOpen U := hD.inter isOpen_ball
  have hzU : z ∈ U := ⟨hz,hnear⟩
  let : NeBot (𝓝[U ∩ Kᶜ] z) := mem_closure_iff_nhdsWithin_neBot.mp
    (hDense.open_subset_closure_inter hU hzU)
  have hlim : Tendsto (fun w => ‖E w‖) (𝓝[U ∩ Kᶜ] z) (𝓝 ‖E z‖) :=
    ((hE.continuousAt (hD.mem_nhds hz)).norm.tendsto).mono_left nhdsWithin_le_nhds
  have hle : ‖E z‖ ≤ ε/2 := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hmatch w ⟨hw.1.1,hw.2⟩]
    have hb : ‖F w-A‖ < ε/2 := by
      simpa only [dist_eq_norm] using hbound ⟨hDΩ hw.1.1,hw.2⟩ hw.1.2
    exact hb.le
  simpa only [dist_zero_right] using hle.trans_lt (half_lt_self hε)

end NLS.ComplexAnalysis
