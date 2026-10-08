import NLS.ZakharovShabat.SourceStandardRootAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Complex gap geometry for the exterior factors in Lemma 28.1 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- The quadratic root controls distance to the midpoint up to the half-gap. -/
theorem midpoint_dist_le_root_add_half_gap (l r z w : ℂ)
    (hw : w^2 = (l-z)*(r-z)) :
    ‖(l+r)/2-z‖ ≤ ‖w‖+‖r-l‖/2 := by
  have hid : ((l+r)/2-z)^2 = w^2+((r-l)/2)^2 := by rw [hw]; ring
  have h := norm_add_le (w^2) (((r-l)/2)^2)
  rw [← hid] at h
  simp only [norm_pow,norm_div,Complex.norm_ofNat] at h
  nlinarith [norm_nonneg ((l+r)/2-z),norm_nonneg w,norm_nonneg (r-l),
    mul_nonneg (norm_nonneg w) (norm_nonneg (r-l))]

/-- Lower bounds for both endpoint distances transfer to either square root. -/
theorem root_norm_ge_endpoint_lower (l r z w : ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hw : w^2 = (l-z)*(r-z)) (hl : A ≤ ‖l-z‖) (hr : A ≤ ‖r-z‖) :
    A ≤ ‖w‖ := by
  have h := congrArg norm hw
  simp only [norm_pow,norm_mul] at h
  have hp := mul_le_mul hl hr hA (norm_nonneg _)
  nlinarith [norm_nonneg w]

/-- A nearby critical point costs at most three half-gaps relative to the root norm. -/
theorem critical_dist_le_root_add_gap (l r z w c : ℂ)
    (hw : w^2 = (l-z)*(r-z)) (hc : ‖c-(l+r)/2‖ ≤ ‖r-l‖) :
    ‖c-z‖ ≤ ‖w‖+(3/2:ℝ)*‖r-l‖ := by
  have h := norm_add_le (c-(l+r)/2) ((l+r)/2-z)
  rw [sub_add_sub_cancel] at h
  linarith [midpoint_dist_le_root_add_half_gap l r z w hw]

/-- Distinct π/5 localization discs give a uniform endpoint separation. -/
theorem localized_endpoint_separation (l z : ℂ) (m n : ℤ) (hmn : m ≠ n)
    (hl : ‖l-(Real.pi:ℂ)*m‖ ≤ Real.pi/5)
    (hz : ‖z-(Real.pi:ℂ)*n‖ ≤ Real.pi/5) :
    (3/2:ℝ)*|((m-n:ℤ):ℝ)| ≤ ‖l-z‖ := by
  have hd : (1:ℝ) ≤ |((m-n:ℤ):ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
  have h := norm_add_le ((Real.pi:ℂ)*m-l) (l-z)
  have h' := norm_add_le ((Real.pi:ℂ)*m-z) (z-(Real.pi:ℂ)*n)
  rw [sub_add_sub_cancel] at h h'
  rw [norm_sub_rev ((Real.pi:ℂ)*m) l] at h
  have he : ‖(Real.pi:ℂ)*m-(Real.pi:ℂ)*n‖ = Real.pi*|((m-n:ℤ):ℝ)| := by
    rw [← mul_sub,norm_mul]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,← Int.cast_sub,
      Complex.norm_intCast]
  rw [he] at h'
  have hb := mul_nonneg (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi-5/2) (sub_nonneg.mpr hd)
  nlinarith [Real.pi_gt_three]

/-- Each exterior quotient is bounded by one plus gap length over index separation. -/
theorem localized_critical_root_factor_le (l r z w c : ℂ) (m n : ℤ) (hmn : m ≠ n)
    (hl : ‖l-(Real.pi:ℂ)*m‖ ≤ Real.pi/5)
    (hr : ‖r-(Real.pi:ℂ)*m‖ ≤ Real.pi/5)
    (hz : ‖z-(Real.pi:ℂ)*n‖ ≤ Real.pi/5)
    (hw : w^2 = (l-z)*(r-z)) (hc : ‖c-(l+r)/2‖ ≤ ‖r-l‖) :
    ‖(c-z)/w‖ ≤ 1+‖r-l‖/|((m-n:ℤ):ℝ)| := by
  have hd : (0:ℝ) < |((m-n:ℤ):ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hmn)
  have hlow : (3/2:ℝ)*|((m-n:ℤ):ℝ)| ≤ ‖w‖ :=
    root_norm_ge_endpoint_lower l r z w _ (by positivity) hw
      (localized_endpoint_separation l z m n hmn hl hz) (localized_endpoint_separation r z m n hmn hr hz)
  have hwpos : 0 < ‖w‖ := by linarith
  have hu := critical_dist_le_root_add_gap l r z w c hw hc
  rw [norm_div]
  apply (div_le_iff₀ hwpos).mpr
  have hp := mul_le_mul_of_nonneg_right hlow (div_nonneg (norm_nonneg (r-l)) hd.le)
  have he : ((3/2:ℝ)*|((m-n:ℤ):ℝ)|)*(‖r-l‖/|((m-n:ℤ):ℝ)|) = (3/2:ℝ)*‖r-l‖ := by
    field_simp
  rw [he] at hp
  nlinarith

/-- A closed localization disc contains the entire straight gap. -/
theorem gap_segment_norm_sub_le (l r z a : ℂ) (R : ℝ)
    (hl : ‖l-a‖ ≤ R) (hr : ‖r-a‖ ≤ R) (hz : z ∈ segment ℝ l r) :
    ‖z-a‖ ≤ R := by
  have h := (convex_closedBall a R).segment_subset
    (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hl)
    (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hr) hz
  simpa only [Metric.mem_closedBall,dist_eq_norm] using h

/-- The midpoint stays in the same localization disc as its endpoints. -/
theorem gap_midpoint_norm_sub_le (l r a : ℂ) (R : ℝ)
    (hl : ‖l-a‖ ≤ R) (hr : ‖r-a‖ ≤ R) : ‖(l+r)/2-a‖ ≤ R := by
  have h := norm_add_le (l-a) (r-a)
  have he : (l+r)/2-a = ((l-a)+(r-a))/2 := by ring
  rw [he,norm_div,Complex.norm_ofNat]
  linarith

/-- Every point of a straight gap is within half its length of the midpoint. -/
theorem gap_segment_midpoint_dist_le (l r c : ℂ) (hc : c ∈ segment ℝ l r) :
    ‖c-(l+r)/2‖ ≤ ‖r-l‖/2 := by
  apply gap_segment_norm_sub_le l r c ((l+r)/2) (‖r-l‖/2) _ _ hc
  · have he : l-(l+r)/2 = -((r-l)/2) := by ring
    simp only [he,norm_neg,norm_div,Complex.norm_ofNat,le_refl]
  · have he : r-(l+r)/2 = (r-l)/2 := by ring
    simp only [he,norm_div,Complex.norm_ofNat,le_refl]

end NLS.ZakharovShabat
