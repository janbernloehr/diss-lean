import NLS.ComplexAnalysis.CoshSquareCoordinate
import NLS.ComplexAnalysis.ContinuousLogarithmUnique
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-! # Real trace levels of a hyperbolic primitive -/

noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

theorem cosh_real_coordinate (z : ℂ) :
    (cosh z).re = Real.cosh z.re * Real.cos z.im := by
  rw [← re_add_im z, cosh_add, cosh_mul_I, sinh_mul_I]
  simp only [← ofReal_cosh, ← ofReal_sinh, ← ofReal_cos, ← ofReal_sin,
    add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one]

theorem cosh_imaginary_coordinate (z : ℂ) :
    (cosh z).im = Real.sinh z.re * Real.sin z.im := by
  rw [← re_add_im z, cosh_add, cosh_mul_I, sinh_mul_I]
  simp only [← ofReal_cosh, ← ofReal_sinh, ← ofReal_cos, ← ofReal_sin,
    add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one]

theorem real_cosh_trace_coordinates (z : ℂ) (d : ℝ) (ht : 2 * cosh z = (d : ℂ)) :
    d = 2 * Real.cosh z.re * Real.cos z.im ∧
      (2 * Real.sinh z.re) * Real.sin z.im = 0 := by
  have hr := congrArg Complex.re ht
  have hi := congrArg Complex.im ht
  have hr2 : (2 * cosh z).re = 2 * (cosh z).re := by simp
  have hi2 : (2 * cosh z).im = 2 * (cosh z).im := by simp
  rw [hr2, cosh_real_coordinate, ofReal_re] at hr
  rw [hi2, cosh_imaginary_coordinate, ofReal_im] at hi
  constructor <;> nlinarith

/-- Away from the imaginary axis, a real trace has absolute value
exactly twice the real hyperbolic cosine of the real part. -/
theorem abs_real_cosh_trace_of_re_ne_zero (z : ℂ) (d : ℝ)
    (ht : 2 * cosh z = (d : ℂ)) (hre : z.re ≠ 0) :
    |d| = 2 * Real.cosh z.re ∧ Real.sin z.im = 0 := by
  obtain ⟨hd, hi⟩ := real_cosh_trace_coordinates z d ht
  have hs : Real.sinh z.re ≠ 0 := fun he => hre (Real.sinh_eq_zero.mp he)
  have hsin : Real.sin z.im = 0 :=
    (mul_eq_zero.mp hi).resolve_left (mul_ne_zero (by norm_num) hs)
  have hc : Real.cos z.im ^ 2 = (1 : ℝ) ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq z.im]
  have habs : |Real.cos z.im| = 1 := by
    rcases eq_or_eq_neg_of_sq_eq_sq (Real.cos z.im) 1 hc with he | he <;> simp [he]
  refine ⟨?_, hsin⟩
  rw [hd, abs_mul, abs_mul, habs, abs_of_pos (Real.cosh_pos z.re)]
  norm_num

/-- A real trace inside the closed band forces a purely imaginary primitive. -/
theorem re_eq_zero_of_real_cosh_trace_band (z : ℂ) (d : ℝ)
    (ht : 2 * cosh z = (d : ℂ)) (hd : |d| ≤ 2) : z.re = 0 := by
  by_contra hre
  have h := (abs_real_cosh_trace_of_re_ne_zero z d ht hre).1
  have hp := Real.one_lt_cosh.mpr hre
  linarith

/-- On the nonnegative sheet, an exterior real trace has exactly its
positive arcosh profile as the primitive's real part. -/
theorem re_eq_arcosh_of_real_cosh_trace_gap (z : ℂ) (d : ℝ)
    (ht : 2 * cosh z = (d : ℂ)) (hre : 0 ≤ z.re) (hd : 2 < |d|) :
    0 < z.re ∧ z.re = Real.arcosh (|d| / 2) ∧ Real.sin z.im = 0 := by
  have hne : z.re ≠ 0 := by
    intro hz
    have hr := (real_cosh_trace_coordinates z d ht).1
    rw [hz, Real.cosh_zero, mul_one] at hr
    have hb : |d| ≤ 2 := by rw [hr, abs_mul]; norm_num; linarith [Real.abs_cos_le_one z.im]
    linarith
  obtain ⟨he, hs⟩ := abs_real_cosh_trace_of_re_ne_zero z d ht hne
  refine ⟨lt_of_le_of_ne hre (Ne.symm hne), ?_, hs⟩
  rw [he, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.arcosh_cosh hre]

/-- A continuous real phase taking only sine-zero values is constant
on a preconnected domain. -/
theorem phase_eq_on_of_sin_eq_zero
    {X : Type*} [TopologicalSpace X] (f : X → ℝ) (S : Set X)
    (hS : IsPreconnected S) (hf : ContinuousOn f S)
    (hsin : ∀ x ∈ S, Real.sin (f x) = 0) (a : X) (ha : a ∈ S) :
    ∀ x ∈ S, f x = f a := by
  let g : X → ℂ := fun x => (2 * (f x : ℂ)) * I
  have hg : ContinuousOn g S :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hf)).mul continuousOn_const
  have hexp (x : X) (hx : x ∈ S) : exp (g x) = 1 := by
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp (hsin x hx)
    have he : g x = (k : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      dsimp only [g]
      rw [← hk]
      push_cast
      ring
    rw [he]
    exact Complex.exp_int_mul_two_pi_mul_I k
  have heq := continuousLogarithms_eqOn g (fun _ => g a) S hS hg continuousOn_const
    (fun x hx => (hexp x hx).trans (hexp a ha).symm) a ha rfl
  intro x hx
  have he := congrArg Complex.im (heq hx)
  simp only [g, mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, mul_one, add_zero] at he
  norm_num at he
  linarith

end NLS.ComplexAnalysis
