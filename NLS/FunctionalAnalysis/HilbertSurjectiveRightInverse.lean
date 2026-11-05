import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
set_option autoImplicit false
namespace NLS.FunctionalAnalysis

/-- Every surjective bounded operator between real Hilbert spaces has a
bounded linear right inverse, by restricting it to the orthogonal kernel
complement. No compactness or finite-dimensional kernel is assumed. -/
theorem exists_hilbert_rightInverse_of_surjective
    {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (T : E →L[ℝ] Y) (hT : Function.Surjective T) :
    ∃ R : Y →L[ℝ] E, T.comp R = ContinuousLinearMap.id ℝ Y := by
  let N := T.ker
  let _ : CompleteSpace N := T.isClosed_ker.completeSpace_coe
  let M := Nᗮ
  let _ : CompleteSpace M := N.isClosed_orthogonal.completeSpace_coe
  let S := T.comp M.subtypeL
  have hSi : Function.Injective S := by
    apply (injective_iff_map_eq_zero S).mpr
    intro x hx
    have hxN : (x : E) ∈ N := hx
    have hh : inner ℝ (x : E) (x : E) = 0 :=
      (Submodule.mem_orthogonal N (x : E)).mp x.property (x : E) hxN
    apply Subtype.ext
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp hh
  have hSs : Function.Surjective S := by
    intro y
    obtain ⟨x,hx⟩ := hT y
    refine ⟨⟨x-N.starProjection x,N.sub_starProjection_mem_orthogonal x⟩,?_⟩
    have hPx : T (N.starProjection x) = 0 := N.starProjection_apply_mem x
    change T (x-N.starProjection x) = y
    rw [map_sub,hPx,sub_zero,hx]
  let V := ContinuousLinearEquiv.ofBijective S (LinearMap.ker_eq_bot.mpr hSi) (LinearMap.range_eq_top.mpr hSs)
  refine ⟨M.subtypeL.comp V.symm.toContinuousLinearMap,?_⟩
  ext y
  exact V.apply_symm_apply y

end NLS.FunctionalAnalysis
