import NLS.Fourier.ContinuousSynthesis

/-! # Pointwise reality of a continuous Fourier synthesis

Conjugate reflection of the actual Fourier coefficients makes the
absolutely convergent physical series real at every real point.
-/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
namespace NLS.Fourier

theorem continuousSynthesis_conj_eq_of_reflection (a : Coeff 1)
    (ha : ∀ n : ℤ, a (-n) = conj (a n)) (x : ℝ) :
    conj (continuousSynthesis a (x : AddCircle (2 : ℝ))) =
      continuousSynthesis a (x : AddCircle (2 : ℝ)) := by
  rw [continuousSynthesis_apply, Complex.conj_tsum]
  simp only [map_mul]
  calc
    _ = ∑' n : ℤ, conj (a (-n))*conj (wave (-n) x) :=
      ((Equiv.neg ℤ).tsum_eq (fun n => conj (a n)*conj (wave n x))).symm
    _ = _ := by simp only [ha, wave_neg, starRingEnd_self_apply]

theorem continuousSynthesis_im_eq_zero_of_reflection (a : Coeff 1)
    (ha : ∀ n : ℤ, a (-n) = conj (a n)) (x : ℝ) :
    (continuousSynthesis a (x : AddCircle (2 : ℝ))).im = 0 := by
  have he := congrArg Complex.im (continuousSynthesis_conj_eq_of_reflection a ha x)
  simp only [conj_im] at he
  linarith

end NLS.Fourier
