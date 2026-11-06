import NLS.FunctionalAnalysis.HilbertSurjectiveRightInverse
import NLS.FunctionalAnalysis.NeumannCompositionBoundGeneral

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.FunctionalAnalysis

/-- A nonzero kernel vector persists under all sufficiently small operator
perturbations of a split surjection. Its correction uses a uniformly
bounded inverse of the perturbed composition with the fixed right inverse. -/
theorem eventually_not_injective_of_rightInverse
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (T : E →L[ℝ] Y) (R : Y →L[ℝ] E)
    (hTR : T.comp R = ContinuousLinearMap.id ℝ Y)
    (v : E) (hv : v ≠ 0) (hTv : T v = 0) :
    ∀ᶠ S : E →L[ℝ] Y in 𝓝 T, ¬Function.Injective S := by
  have hc : Continuous (fun S : E →L[ℝ] Y => ‖S.comp R-ContinuousLinearMap.id ℝ Y‖) := by fun_prop
  have hs : Continuous (fun S : E →L[ℝ] Y => (2*‖R‖)*‖S v‖) := by fun_prop
  have hec : ∀ᶠ S : E →L[ℝ] Y in 𝓝 T, ‖S.comp R-ContinuousLinearMap.id ℝ Y‖ < 1/2 := by
    have hh := hc.continuousAt.tendsto.eventually (gt_mem_nhds (show
      ‖T.comp R-ContinuousLinearMap.id ℝ Y‖ < 1/2 by rw [hTR,sub_self,norm_zero]; norm_num))
    exact hh
  have hes : ∀ᶠ S : E →L[ℝ] Y in 𝓝 T, (2*‖R‖)*‖S v‖ < ‖v‖ := by
    have hh := hs.continuousAt.tendsto.eventually (gt_mem_nhds (show
      (2*‖R‖)*‖T v‖ < ‖v‖ by rw [hTv,norm_zero,mul_zero]; exact norm_pos_iff.mpr hv))
    exact hh
  filter_upwards [hec,hes] with S hSc hSv
  have hnear : ‖(ContinuousLinearMap.id ℝ Y).comp
      (ContinuousLinearMap.id ℝ Y-S.comp R)‖ ≤ (1/2 : ℝ) := by
    rw [ContinuousLinearMap.id_comp,norm_sub_rev]
    exact hSc.le
  obtain ⟨Q,hQ,hQ',hQnorm⟩ := exists_inverse_norm_le_two_mul_of_composition_near
    (S.comp R) (ContinuousLinearMap.id ℝ Y) (ContinuousLinearMap.id ℝ Y)
    (by ext y; rfl) (by ext y; rfl) hnear
  have hQ2 : ‖Q‖ ≤ 2 := by
    have hi : ‖ContinuousLinearMap.id ℝ Y‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    linarith

  let w := v-R (Q (S v))
  have hSw : S w = 0 := by
    have he := congrArg (fun A : Y →L[ℝ] Y => A (S v)) hQ
    change S (R (Q (S v))) = S v at he
    change S (v-R (Q (S v))) = 0
    rw [map_sub,he,sub_self]
  have hbound : ‖R (Q (S v))‖ < ‖v‖ := by
    calc
      _ ≤ ‖R‖*(‖Q‖*‖S v‖) := (R.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (Q.le_opNorm _) (norm_nonneg R))
      _ ≤ ‖R‖*(2*‖S v‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hQ2 (norm_nonneg (S v))) (norm_nonneg R)
      _ = (2*‖R‖)*‖S v‖ := by ring
      _ < _ := hSv
  have hw : w ≠ 0 := by
    intro hz
    have he : v = R (Q (S v)) := sub_eq_zero.mp hz
    exact (lt_irrefl ‖v‖) (by simpa only [←he] using hbound)
  intro hSi
  exact hw (hSi (hSw.trans (map_zero S).symm))

/-- Noninjectivity is open at any surjective bounded real Hilbert operator. -/
theorem eventually_not_injective_of_surjective
    {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (T : E →L[ℝ] Y) (hT : Function.Surjective T) (hN : ¬Function.Injective T) :
    ∀ᶠ S : E →L[ℝ] Y in 𝓝 T, ¬Function.Injective S := by
  obtain ⟨R,hR⟩ := exists_hilbert_rightInverse_of_surjective T hT
  have he : ¬∀ v : E, T v = 0 → v = 0 := by
    intro hh
    exact hN ((injective_iff_map_eq_zero T).mpr hh)
  push Not at he
  obtain ⟨v,hTv,hv⟩ := he
  exact eventually_not_injective_of_rightInverse T R hR v hv hTv

end NLS.FunctionalAnalysis
