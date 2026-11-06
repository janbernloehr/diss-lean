import NLS.ComplexAnalysis.AnalyticOpenInverse

/-! # Reality of a local inverse at an arbitrary fixed real base -/
noncomputable section
set_option autoImplicit false
open Set Metric
namespace NLS.ComplexAnalysis

/-- A local inverse preserves the fixed real form near ANY fixed base.
Only the actual local injectivity and conjugation identity are used. -/
theorem exists_fixed_inverse_neighborhood_at
    {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]
    (F : X → Y) (G : Y → X) (J : X → X) (K : Y → Y)
    (hJ : Isometry J) (V : Set X) (W : Set Y) (hV : IsOpen V) (hW : IsOpen W)
    (a : X) (ha : a ∈ V) (hJa : J a = a) (hFa : F a ∈ W)
    (hG : ContinuousOn G W) (hinj : InjOn F V)
    (hleft : ∀ x ∈ V, G (F x) = x) (hright : ∀ y ∈ W, G y ∈ V ∧ F (G y) = y)
    (hconj : ∀ x ∈ V, F (J x) = K (F x)) :
    ∃ U : Set Y, IsOpen U ∧ F a ∈ U ∧ U ⊆ W ∧
      ∀ y ∈ U, K y = y → J (G y) = G y := by
  obtain ⟨δ,hδ,hδV⟩ := Metric.isOpen_iff.mp hV a ha
  let U := W ∩ G ⁻¹' ball a δ
  refine ⟨U,hG.isOpen_inter_preimage hW isOpen_ball,⟨hFa,?_⟩,inter_subset_left,?_⟩
  · change G (F a) ∈ ball a δ
    rw [hleft a ha]
    exact mem_ball_self hδ
  · intro y hy hKy
    obtain ⟨hGy,hFGy⟩ := hright y hy.1
    have hJGy : J (G y) ∈ V := by
      apply hδV
      rw [mem_ball,←hJa,hJ.dist_eq]
      exact hy.2
    apply hinj hJGy hGy
    rw [hconj (G y) hGy,hFGy,hKy]

end NLS.ComplexAnalysis
