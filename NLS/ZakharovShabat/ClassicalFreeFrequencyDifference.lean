import NLS.ZakharovShabat.ClassicalRemainderTimeRegularity

/-! # Comparing two nearby free evolutions

A small spectral displacement from the real axis gives a uniformly small
free-solution difference. Time differentiation costs one spectral factor;
when the displacement is O(1/|n|), this remains uniformly bounded.
-/

noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- The difference of the free evolutions at a complex frequency and a real reference. -/
def classicalFreeFrequencyDifference (z : ℂ) (x : ℝ) (v : ℂ × ℂ) (t : ℝ) : ℂ × ℂ :=
  classicalFreeVector z v t-classicalFreeVector (x : ℂ) v t

theorem contDiff_classicalFreeFrequencyDifference (z : ℂ) (x : ℝ) (v : ℂ × ℂ) :
    ContDiff ℝ 1 (classicalFreeFrequencyDifference z x v) :=
  (contDiff_classicalFreeVector z v).sub (contDiff_classicalFreeVector x v)

private theorem norm_exp_frequency_sub_le (c z : ℂ) (x t : ℝ)
    (hc : ‖c‖ = 1) (hcre : c.re = 0) (hz : ‖z-(x : ℂ)‖ ≤ 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖exp (c*z*t)-exp (c*x*t)‖ ≤ 2*‖z-(x : ℂ)‖ := by
  have he : exp (c*z*t)-exp (c*x*t) = exp (c*x*t)*(exp (c*(z-x)*t)-1) := by
    rw [mul_sub,mul_one,← exp_add]
    congr 2
    ring
  have hex : ‖exp (c*x*t)‖ = 1 := by
    simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im,hcre]
  have hn : ‖c*(z-x)*t‖ = ‖z-(x : ℂ)‖*t := by
    simp only [norm_mul,hc,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
  have hsmall : ‖c*(z-x)*t‖ ≤ 1 := by rw [hn]; nlinarith [norm_nonneg (z-(x : ℂ)),ht.2]
  rw [he,norm_mul,hex,one_mul]
  exact (norm_exp_sub_one_le hsmall).trans (by rw [hn]; nlinarith [norm_nonneg (z-(x : ℂ)),ht.2])

/-- Uniform value bound for a unit-size or smaller spectral displacement. -/
theorem norm_classicalFreeFrequencyDifference_le
    (z : ℂ) (x : ℝ) (v : ℂ × ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) (t : Icc (0 : ℝ) 1) :
    ‖classicalFreeFrequencyDifference z x v t‖ ≤ 2*‖z-(x : ℂ)‖*‖v‖ := by
  apply norm_prod_le_iff.mpr
  constructor
  · change ‖exp (-I*z*t)*v.1-exp (-I*x*t)*v.1‖ ≤ _
    rw [← sub_mul,norm_mul]
    exact mul_le_mul (norm_exp_frequency_sub_le (-I) z x t (by simp) (by simp) hz t.property)
      (norm_fst_le v) (norm_nonneg _) (by positivity)
  · change ‖exp (I*z*t)*v.2-exp (I*x*t)*v.2‖ ≤ _
    rw [← sub_mul,norm_mul]
    exact mul_le_mul (norm_exp_frequency_sub_le I z x t (by simp) (by simp) hz t.property)
      (norm_snd_le v) (norm_nonneg _) (by positivity)

/-- The real-reference free evolution preserves the maximum norm of the initial vector. -/
theorem norm_classicalFreeVector_real (x t : ℝ) (v : ℂ × ℂ) :
    ‖classicalFreeVector (x : ℂ) v t‖ = ‖v‖ := by
  simp [classicalFreeVector,Prod.norm_def,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

/-- The difference's derivative separates its small error from the small frequency displacement. -/
theorem hasDerivAt_classicalFreeFrequencyDifference (z : ℂ) (x t : ℝ) (v : ℂ × ℂ) :
    HasDerivAt (classicalFreeFrequencyDifference z x v)
      (-I*z*(classicalFreeFrequencyDifference z x v t).1-I*(z-x)*(classicalFreeVector x v t).1,
        I*z*(classicalFreeFrequencyDifference z x v t).2+I*(z-x)*(classicalFreeVector x v t).2) t := by
  apply ((hasDerivAt_classicalFreeVector z v t).sub (hasDerivAt_classicalFreeVector x v t)).congr_deriv
  apply Prod.ext <;> dsimp [classicalFreeFrequencyDifference] <;> ring

/-- Time differentiation costs one spectral factor and retains the small displacement factor. -/
theorem norm_deriv_classicalFreeFrequencyDifference_le
    (z : ℂ) (x : ℝ) (v : ℂ × ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) (t : Icc (0 : ℝ) 1) :
    ‖deriv (classicalFreeFrequencyDifference z x v) t‖ ≤ (2*‖z‖+1)*‖z-(x : ℂ)‖*‖v‖ := by
  have hn : ‖deriv (classicalFreeFrequencyDifference z x v) t‖ ≤
      ‖z‖*‖classicalFreeFrequencyDifference z x v t‖+‖z-(x : ℂ)‖*‖classicalFreeVector x v t‖ := by
    rw [(hasDerivAt_classicalFreeFrequencyDifference z x t v).deriv]
    apply norm_prod_le_iff.mpr
    constructor
    · apply (norm_sub_le _ _).trans
      simp only [norm_mul,norm_neg,norm_I,one_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_fst_le _) (norm_nonneg _))
    · apply (norm_add_le _ _).trans
      simp only [norm_mul,norm_I,one_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (norm_snd_le _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_snd_le _) (norm_nonneg _))
  rw [norm_classicalFreeVector_real] at hn
  have h := norm_classicalFreeFrequencyDifference_le z x v hz t
  nlinarith [norm_nonneg z]

end NLS.ZakharovShabat
