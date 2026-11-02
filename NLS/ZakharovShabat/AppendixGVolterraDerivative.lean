import NLS.ComplexAnalysis.AppendixGBornDerivative
import NLS.ZakharovShabat.ClassicalRemainderDerivativeBound

/-! # The corrected differentiated Volterra identity in Appendix G

The free first component has derivative -i*z and the second +i*z.
These signs are retained in the derivative of the actual remainder.
-/
noncomputable section
open Set Complex MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The first Born vector satisfies its actual forced free equation. -/
theorem appendixG_hasDerivAt_classicalFirstBornVector
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : ℝ) :
    HasDerivAt (classicalFirstBornVector φ z v)
      (-I*z*(classicalFirstBornVector φ z v t).1+
          I*exp (I*z*t)*(extend φ t).1*v.2,
        I*z*(classicalFirstBornVector φ z v t).2-
          I*exp (-I*z*t)*(extend φ t).2*v.1) t := by
  have hm := appendixG_hasDerivAt_oscillatoryIntegral (-I*z) _ (continuous_extend φ).fst t
  have hp := appendixG_hasDerivAt_oscillatoryIntegral (I*z) _ (continuous_extend φ).snd t
  have hd := ((hm.const_mul I).mul_const v.2).prodMk ((hp.const_mul (-I)).mul_const v.1)
  apply hd.congr_deriv
  apply Prod.ext <;> dsimp [classicalFirstBornVector] <;>
    simp only [neg_mul,neg_neg] <;> ring

/-- Differentiate the actual Volterra equation with the free-mode signs.
The first spectral integral has -i*z and the second has +i*z. -/
theorem appendixG_remainder_derivative_duhamel
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    deriv (classicalSolutionRemainder φ z v) t =
      ((deriv (classicalFirstBornVector φ z v) t).1+
          I*(φ t).1*(classicalSolutionRemainder φ z v t).2-
          I*z*(∫ s in (0 : ℝ)..t.val, exp (-I*z*(t.val-s))*
            (I*(extend φ s).1*(classicalSolutionRemainder φ z v s).2)),
        (deriv (classicalFirstBornVector φ z v) t).2-
          I*(φ t).2*(classicalSolutionRemainder φ z v t).1+
          I*z*(∫ s in (0 : ℝ)..t.val, exp (I*z*(t.val-s))*
            ((-I)*(extend φ s).2*(classicalSolutionRemainder φ z v s).1))) := by
  rw [(hasDerivAt_classicalSolutionRemainder φ z v t).deriv,
    (appendixG_hasDerivAt_classicalFirstBornVector φ z v t).deriv,extend_coe]
  apply Prod.ext
  · have h := classicalSolutionRemainder_fst_duhamel φ z v t
    dsimp only [Prod.fst] at h ⊢
    simp only [classicalSolutionRemainder,Prod.fst_sub,Prod.snd_sub,classicalFreeVector] at h ⊢
    linear_combination (-I*z)*h
  · have h := classicalSolutionRemainder_snd_duhamel φ z v t
    dsimp only [Prod.snd] at h ⊢
    simp only [classicalSolutionRemainder,Prod.fst_sub,Prod.snd_sub,classicalFreeVector] at h ⊢
    linear_combination (I*z)*h

end NLS.ZakharovShabat
