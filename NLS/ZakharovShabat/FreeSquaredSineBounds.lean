import NLS.ZakharovShabat.FreeSineQuotientAnalytic
import NLS.ComplexAnalysis.EntireIncrementBound

/-!
# Linear bounds for the free squared sine quotient

The squared quotient is a translate of its zero-index version, has value
one and derivative zero at each center, and has common linear increment
and derivative bounds on all free discs of any fixed radius.
-/

open Set Complex
namespace NLS.ZakharovShabat

/-- The translating cosine disappears after squaring. -/
theorem freeSineQuotient_sq_translate (n : ℤ) (z : ℂ) :
    (freeSineQuotient n z)^2 = (freeSineQuotient 0 (z-(Real.pi : ℂ)*n))^2 := by
  have hs := sin_sq_add_cos_sq ((Real.pi : ℂ)*n)
  have hz : sin ((Real.pi : ℂ)*n) = 0 := by simpa [mul_comm] using sin_int_mul_pi n
  have hc : cos ((Real.pi : ℂ)*n)^2 = 1 := by simpa only [hz,zero_pow (by decide : 2 ≠ 0),zero_add] using hs
  simp only [freeSineQuotient,mul_pow,hc,one_mul,Int.cast_zero,mul_zero,cos_zero,sub_zero]

/-- The squared filled quotient takes value one at every signed free center. -/
theorem freeSineQuotient_sq_center (n : ℤ) : (freeSineQuotient n ((Real.pi : ℂ)*n))^2 = 1 := by
  rw [freeSineQuotient_sq_translate]
  simp [freeSineQuotient,Complex.deriv_sin]

/-- The zero-index filled sine quotient is even. -/
theorem freeSineQuotient_zero_neg (z : ℂ) : freeSineQuotient 0 (-z) = freeSineQuotient 0 z := by
  by_cases hz : z = 0
  · subst z; simp
  · rw [freeSineQuotient_eq_div 0 (-z) (by simpa using neg_ne_zero.mpr hz),
      freeSineQuotient_eq_div 0 z (by simpa using hz)]
    simp

/-- Evenness forces the derivative of the filled zero-index quotient to vanish at zero. -/
theorem deriv_freeSineQuotient_zero_center : deriv (freeSineQuotient 0) 0 = 0 := by
  have hd := ((differentiable_freeSineQuotient 0) 0).hasDerivAt
  have hn := hd.comp_of_eq 0 (hasDerivAt_neg (0 : ℂ)) (by simp)
  change HasDerivAt (fun z => freeSineQuotient 0 (-z)) (deriv (freeSineQuotient 0) 0*(-1)) 0 at hn
  have he : (fun z => freeSineQuotient 0 (-z)) = freeSineQuotient 0 := funext freeSineQuotient_zero_neg
  rw [he] at hn
  have h := hd.unique hn
  linear_combination h / 2

/-- Derivatives of squared free quotients translate by the same free center. -/
theorem deriv_freeSineQuotient_sq_translate (n : ℤ) (z : ℂ) :
    deriv (fun w => (freeSineQuotient n w)^2) z =
      deriv (fun w => (freeSineQuotient 0 w)^2) (z-(Real.pi : ℂ)*n) := by
  have he : (fun w => (freeSineQuotient n w)^2) = fun w => (freeSineQuotient 0 (w-(Real.pi : ℂ)*n))^2 :=
    funext (freeSineQuotient_sq_translate n)
  rw [he]
  have hd := (((differentiable_freeSineQuotient 0).pow 2) (z-(Real.pi : ℂ)*n)).hasDerivAt.comp z
    ((hasDerivAt_id z).sub_const ((Real.pi : ℂ)*n))
  change HasDerivAt (fun w => (freeSineQuotient 0 (w-(Real.pi : ℂ)*n))^2)
    (deriv (fun w => (freeSineQuotient 0 w)^2) (z-(Real.pi : ℂ)*n)*1) z at hd
  simpa only [mul_one] using hd.deriv

/-- The squared free quotient has derivative zero at every free center. -/
theorem deriv_freeSineQuotient_sq_center (n : ℤ) :
    deriv (fun w => (freeSineQuotient n w)^2) ((Real.pi : ℂ)*n) = 0 := by
  rw [deriv_freeSineQuotient_sq_translate,sub_self]
  have h := (((differentiable_freeSineQuotient 0) 0).hasDerivAt.pow 2).deriv
  change deriv (fun w => (freeSineQuotient 0 w)^2) 0 = _ at h
  simpa only [deriv_freeSineQuotient_zero_center,mul_zero] using h

/-- One constant bounds the squared-quotient value and derivative deviations on every fixed-radius free disc. -/
theorem exists_freeSquaredSine_displacement_bounds (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ r →
      ‖(freeSineQuotient n z)^2-1‖ ≤ C*‖z-(Real.pi : ℂ)*n‖ ∧
      ‖deriv (fun w => (freeSineQuotient n w)^2) z‖ ≤ C*‖z-(Real.pi : ℂ)*n‖ := by
  have hq : Differentiable ℂ (fun z => (freeSineQuotient 0 z)^2) := (differentiable_freeSineQuotient 0).pow 2
  have hd : Differentiable ℂ (deriv (fun z => (freeSineQuotient 0 z)^2)) := fun z =>
    (((analyticOnNhd_freeSineQuotient 0).pow 2) z (mem_univ _)).deriv.differentiableAt
  obtain ⟨A,hA,ha⟩ := NLS.ComplexAnalysis.exists_bound_entire_increment _ hq 0 r
  obtain ⟨B,hB,hb⟩ := NLS.ComplexAnalysis.exists_bound_entire_increment _ hd 0 r
  have hq0 : (freeSineQuotient 0 0)^2 = 1 := by simpa using freeSineQuotient_sq_center 0
  have hd0 : deriv (fun w => (freeSineQuotient 0 w)^2) 0 = 0 := by simpa using deriv_freeSineQuotient_sq_center 0
  refine ⟨max A B,hA.trans (le_max_left _ _),fun n z hz => ?_⟩
  constructor
  · rw [freeSineQuotient_sq_translate]
    have h := ha (z-(Real.pi : ℂ)*n) (by simpa using hz)
    simp only [hq0,sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · rw [deriv_freeSineQuotient_sq_translate]
    have h := hb (z-(Real.pi : ℂ)*n) (by simpa using hz)
    simp only [hd0,sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end NLS.ZakharovShabat
