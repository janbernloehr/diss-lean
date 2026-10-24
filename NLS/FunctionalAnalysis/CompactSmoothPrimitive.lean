import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Compact smooth primitives of zero-integral test functions

This is the test-function ingredient in recovering absolutely continuous
representatives from weak derivatives on the real line.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Function
open scoped ContDiff
namespace NLS.FunctionalAnalysis

/-- A compactly supported smooth function on the real line has a compact
smooth primitive whenever its integral vanishes. -/
theorem exists_contDiff_compact_primitive_of_integral_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hi : (∫ t : ℝ, f t) = 0) :
    ∃ F : ℝ → E, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ ∀ t, HasDerivAt F (f t) t := by
  obtain ⟨C,hC,hbound⟩ := hc.isBounded.exists_pos_norm_lt
  let F : ℝ → E := fun t => ∫ s in -C..t, f s
  have hd (t : ℝ) : HasDerivAt F (f t) t :=
    (hf.continuous.integral_hasStrictDerivAt (-C) t).hasDerivAt
  refine ⟨F,?_,?_,hd⟩
  · apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun t => (hd t).differentiableAt,?_⟩
    have he : deriv F = f := funext (fun t => (hd t).deriv)
    rw [he]
    exact hf
  · apply HasCompactSupport.of_support_subset_isCompact (K := Icc (-C) C) isCompact_Icc
    intro t ht
    by_contra hnot
    have hcases : t < -C ∨ C < t := by
      simpa only [mem_Icc,not_and_or,not_le] using hnot
    have hz : F t = 0 := by
      rcases hcases with hleft | hright
      · change (∫ s in -C..t, f s) = 0
        calc
          (∫ s in -C..t, f s) = ∫ _ in -C..t, (0 : E) := by
            apply intervalIntegral.integral_congr
            intro s hs
            have hs' : s ∈ Icc t (-C) := by simpa only [uIcc_of_ge hleft.le] using hs
            apply image_eq_zero_of_notMem_tsupport
            intro hmem
            have hb := hbound s hmem
            rw [Real.norm_eq_abs] at hb
            have hl := (abs_lt.mp hb).1
            linarith [hs'.2]
          _ = 0 := intervalIntegral.integral_zero
      · change (∫ s in -C..t, f s) = 0
        rw [intervalIntegral.integral_eq_integral_of_support_subset,hi]
        intro s hs
        have hb := hbound s (subset_tsupport f hs)
        rw [Real.norm_eq_abs] at hb
        exact ⟨(abs_lt.mp hb).1,(abs_lt.mp hb).2.le.trans hright.le⟩
    exact ht hz

end NLS.FunctionalAnalysis
