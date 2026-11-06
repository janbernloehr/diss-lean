import NLS.ComplexAnalysis.CompactParameterBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



/-- Retain a whole open spectral neighborhood of the compact slice in
the local uniform bound, together with the joint domain inclusion. -/
theorem exists_local_uniform_bound_near_compact_of_continuousOn
    {E : Type*} [TopologicalSpace E]
    (f : ℂ × E → ℂ) (D : Set (ℂ × E)) (hD : IsOpen D)
    (hf : ContinuousOn f D) (K : Set ℂ) (hK : IsCompact K)
    (x : E) (hKx : ∀ z∈K, (z,x)∈D) :
    ∃ A : Set ℂ, ∃ U : Set E, ∃ B : ℝ,
      IsOpen A ∧ IsOpen U ∧ K⊆A ∧ x∈U ∧ 0<B ∧
      ∀ y∈U, ∀ z∈A, (z,y)∈D ∧ ‖f (z,y)‖≤B := by
  have hslice : K ×ˢ ({x} : Set E)⊆D := by
    rintro ⟨z,y⟩ ⟨hz,hy⟩
    change y=x at hy
    subst y
    exact hKx z hz
  obtain ⟨T,hKT,hTo,hTb⟩ := Metric.exists_isOpen_isBounded_image_of_isCompact_of_continuousOn
    (hK.prod isCompact_singleton) hD hslice hf
  obtain ⟨A,U,hA,hU,hKA,hxU,hAU⟩ := generalized_tube_lemma hK isCompact_singleton
    (hTo.inter hD) (fun t ht => ⟨hKT ht,hslice ht⟩)
  obtain ⟨B,hB,hbound⟩ := hTb.exists_pos_norm_le
  refine ⟨A,U,B,hA,hU,hKA,hxU (mem_singleton x),hB,?_⟩
  intro y hy z hz
  have hzy : (z,y)∈T∩D := hAU ⟨hz,hy⟩
  exact ⟨hzy.2,hbound _ ⟨(z,y),hzy.1,rfl⟩⟩

end NLS.ComplexAnalysis
