import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic

/-! # A set containing both nonreal half-planes and a real interval is preconnected. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ComplexAnalysis

theorem isPreconnected_of_contains_nonreal_and_real_interval
    (S : Set ℂ) (a b : ℝ) (hab : a < b)
    (hnonreal : ∀ z : ℂ, z.im ≠ 0 → z ∈ S)
    (hinterval : ∀ z : ℂ, z.re ∈ Ioo a b → z ∈ S) : IsPreconnected S := by
  let U : Set ℂ := {z | 0 < z.im}
  let L : Set ℂ := {z | z.im < 0}
  let V : Set ℂ := {z | a < z.re} ∩ {z | z.re < b}
  let c : ℝ := (a+b)/2
  have hc : a < c ∧ c < b := by dsimp only [c]; constructor <;> linarith
  have hV : IsPreconnected V := ((convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt b)).isPreconnected
  have hu : (c : ℂ)+I ∈ U ∩ V := by
    simp only [mem_inter_iff,U,V,mem_ofPred_eq,add_im,add_re,ofReal_im,ofReal_re,I_im,I_re,zero_add,add_zero]
    exact ⟨by norm_num,hc⟩
  have hl : (c : ℂ)-I ∈ (U ∪ V) ∩ L := by
    simp only [mem_inter_iff,mem_union,U,V,L,mem_ofPred_eq,sub_im,sub_re,ofReal_im,ofReal_re,I_im,I_re,zero_sub,sub_zero]
    exact ⟨Or.inr hc,by norm_num⟩
  have hT : IsPreconnected ((U ∪ V) ∪ L) :=
    IsPreconnected.union' ⟨_,hl⟩ (IsPreconnected.union' ⟨_,hu⟩
      (convex_halfSpace_im_gt 0).isPreconnected hV) (convex_halfSpace_im_lt 0).isPreconnected
  apply hT.subset_closure
  · intro z hz
    rcases hz with (hu | hv) | hl
    · exact hnonreal z (ne_of_gt hu)
    · exact hinterval z hv
    · exact hnonreal z (ne_of_lt hl)
  · intro z _
    by_cases hi : z.im = 0
    · apply Metric.mem_closure_iff.mpr
      intro ε hε
      refine ⟨z+(ε/2 : ℝ)*I,Or.inl (Or.inl ?_),?_⟩
      · simp only [U,mem_ofPred_eq,add_im,mul_im,ofReal_re,I_im,ofReal_im,I_re,hi,zero_mul,mul_one,add_zero,zero_add]
        positivity
      · rw [dist_eq_norm,sub_add_cancel_left,norm_neg,norm_mul,norm_real,Real.norm_eq_abs,norm_I,mul_one,abs_of_pos (by positivity : 0 < ε/2)]
        linarith
    · apply subset_closure
      rcases lt_or_gt_of_ne hi with hn | hp
      · exact Or.inr hn
      · exact Or.inl (Or.inl hp)


end NLS.ComplexAnalysis
