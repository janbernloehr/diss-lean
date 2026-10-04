import NLS.SequenceSpaces.NonnegativeActions

/-! # Nearby real lifts of a scalar action

Rescaling a real coordinate pair by a nearby real square root preserves
its direction and realizes any nonnegative action. At the zero pair we
choose the first axis. Each coordinate displacement has a uniform square
bound, without a lower bound on the original radius.
-/
noncomputable section
namespace NLS.Coeff

/-- Any nonnegative action has a real pair representative near a prescribed
real pair, with a square-root bound for each coordinate displacement. -/
theorem exists_nearby_real_action_pair (x y b : ℂ)
    (hx : x.im = 0) (hy : y.im = 0) (hb : b.im = 0 ∧ 0 ≤ b.re) :
    ∃ u v : ℂ, u.im = 0 ∧ v.im = 0 ∧ (u^2+v^2)/2 = b ∧
      ‖u-x‖^2 ≤ 2*‖b-(x^2+y^2)/2‖ ∧ ‖v-y‖^2 ≤ 2*‖b-(x^2+y^2)/2‖ := by
  obtain ⟨a, ha, _⟩ := ComplexAnalysis.exists_nearby_squareRoot 0 (x^2+y^2)
  have har : a.im = 0 := by
    apply im_eq_zero_of_sq_nonnegative
    · rw [ha]
      simp [pow_two, hx, hy]
    · rw [ha]
      simp [pow_two, hx, hy]
      nlinarith [sq_nonneg x.re, sq_nonneg y.re]
  have hnorm : ‖a‖^2 = ‖x‖^2 + ‖y‖^2 := by
    have h := congrArg Complex.re ha
    simp only [Complex.sq_norm, Complex.normSq_apply, har, hx, hy, mul_zero, add_zero]
    simpa [pow_two, har, hx, hy] using h
  obtain ⟨s, hs, hd⟩ := ComplexAnalysis.exists_nearby_squareRoot a (2*b)
  have hsr : s.im = 0 := by
    apply im_eq_zero_of_sq_nonnegative
    · rw [hs]
      simp [hb.1]
    · rw [hs]
      simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb.2
  have hbound : ‖s-a‖^2 ≤ 2*‖b-(x^2+y^2)/2‖ := by
    have he : 2*b-a^2 = 2*(b-(x^2+y^2)/2) := by rw [ha]; ring
    simpa [he, norm_mul] using hd
  by_cases ha0 : a = 0
  · have hx0 : x = 0 := norm_eq_zero.mp (by simp only [ha0, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hnorm; nlinarith [norm_nonneg x, sq_nonneg ‖y‖])
    have hy0 : y = 0 := norm_eq_zero.mp (by simp only [ha0, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hnorm; nlinarith [norm_nonneg y, sq_nonneg ‖x‖])
    refine ⟨s, 0, hsr, by simp, ?_, ?_, ?_⟩
    · rw [zero_pow (by decide : 2 ≠ 0), add_zero, hs]
      ring
    · simpa only [hx0, ha0] using hbound
    · simp [hy0]
  · have hcoord (c : ℂ) (hc : ‖c‖ ≤ ‖a‖) :
        ‖s*c/a-c‖^2 ≤ 2*‖b-(x^2+y^2)/2‖ := by
      have hratio : ‖c/a‖ ≤ 1 := by
        rw [norm_div]
        exact (div_le_one (norm_pos_iff.mpr ha0)).mpr hc
      have he : s*c/a-c = (s-a)*(c/a) := by field_simp
      calc
        ‖s*c/a-c‖^2 = (‖s-a‖*‖c/a‖)^2 := by rw [he, norm_mul]
        _ ≤ ‖s-a‖^2 := by
          apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          exact mul_le_of_le_one_right (norm_nonneg _) hratio
        _ ≤ _ := hbound
    refine ⟨s*x/a, s*y/a, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Complex.div_im, Complex.mul_im, hsr, hx, har]
    · simp [Complex.div_im, Complex.mul_im, hsr, hy, har]
    · calc
        ((s*x/a)^2+(s*y/a)^2)/2 = (s^2/a^2)*(x^2+y^2)/2 := by ring
        _ = b := by rw [← ha, div_mul_cancel₀ _ (pow_ne_zero 2 ha0), hs]; ring
    · apply hcoord x
      nlinarith [sq_nonneg ‖y‖, norm_nonneg a, norm_nonneg x]
    · apply hcoord y
      nlinarith [sq_nonneg ‖x‖, norm_nonneg a, norm_nonneg y]

end NLS.Coeff
