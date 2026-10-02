import NLS.ZakharovShabat.ClassicalRemainderBound
import NLS.ZakharovShabat.ClassicalHorizontalStripBounds

/-! # Uniform time-derivative bounds for the fundamental-solution error

Subtracting the free ODE leaves a spectral factor multiplying only
the decaying remainder. Its inverse-frequency bound cancels that
factor, while the full solution already has imaginary-height growth.
This supplies the derivative estimate needed before the interpolation
step in Appendix G.3.
-/

noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The explicit free vector solves the free first-order system. -/
theorem hasDerivAt_classicalFreeVector (z : ℂ) (v : ℂ × ℂ) (t : ℝ) :
    HasDerivAt (classicalFreeVector z v)
      (-I*z*(classicalFreeVector z v t).1,I*z*(classicalFreeVector z v t).2) t := by
  have hd := ((hasDerivAt_complex_exp_mul (-I*z) t).mul_const v.1).prodMk
    ((hasDerivAt_complex_exp_mul (I*z) t).mul_const v.2)
  convert hd using 1
  · rfl
  · apply Prod.ext <;> dsimp [classicalFreeVector] <;> ring

/-- The derivative of the actual remainder retains the full solution
in the potential term, and only the remainder in the spectral term. -/
theorem hasDerivAt_classicalSolutionRemainder
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalSolutionRemainder φ z v)
      (-I*z*(classicalSolutionRemainder φ z v t).1+I*(φ t).1*(classicalSolution φ z v t).2,
       I*z*(classicalSolutionRemainder φ z v t).2-I*(φ t).2*(classicalSolution φ z v t).1) t := by
  have hd := (hasDerivAt_classicalSolution φ z v t).sub (hasDerivAt_classicalFreeVector z v t)
  apply hd.congr_deriv
  apply Prod.ext <;> dsimp [classicalODECoefficient_apply,classicalSolutionRemainder] <;> ring

/-- A pointwise derivative estimate that keeps the decaying spectral
factor separate from the full-solution growth term. -/
theorem norm_deriv_classicalSolutionRemainder_le
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    ‖deriv (classicalSolutionRemainder φ z v) t‖ ≤
      ‖z‖*‖classicalSolutionRemainder φ z v t‖+‖φ‖*‖classicalSolution φ z v t‖ := by
  rw [(hasDerivAt_classicalSolutionRemainder φ z v t).deriv]
  apply norm_prod_le_iff.mpr
  constructor
  · apply (norm_add_le _ _).trans
    simp only [norm_mul,norm_neg,norm_I,one_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le _) (norm_nonneg _))
      (mul_le_mul ((norm_fst_le (φ t)).trans (φ.norm_coe_le_norm t)) (norm_snd_le _)
        (norm_nonneg _) (norm_nonneg _))
  · apply (norm_sub_le _ _).trans
    simp only [norm_mul,norm_I,one_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (norm_snd_le _) (norm_nonneg _))
      (mul_le_mul ((norm_snd_le (φ t)).trans (φ.norm_coe_le_norm t)) (norm_fst_le _)
        (norm_nonneg _) (norm_nonneg _))

/-- After exponential normalization the derivative is bounded
independently of the nonzero spectral parameter. -/
theorem norm_deriv_classicalSolutionRemainder_weighted_le
    (φ : Curve (ℂ × ℂ))
    (hf : AbsolutelyContinuousOnInterval (fun s => (extend φ s).1) 0 1)
    (hg : AbsolutelyContinuousOnInterval (fun s => (extend φ s).2) 0 1)
    (hfi : IntervalIntegrable (deriv (fun s => (extend φ s).1)) volume 0 1)
    (hgi : IntervalIntegrable (deriv (fun s => (extend φ s).2)) volume 0 1)
    (z : ℂ) (hz : z ≠ 0) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    Real.exp (-(|z.im| * t.val))*‖deriv (classicalSolutionRemainder φ z v) t‖ ≤
      (classicalFirstBornUniformBudget φ/2+‖φ‖)*‖v‖*Real.exp ‖φ‖ := by
  let E := Real.exp (-(|z.im| * t.val))
  have hS : E*‖classicalSolution φ z v t‖ ≤ ‖v‖*Real.exp ‖φ‖ := by
    have h := mul_le_mul_of_nonneg_left (norm_classicalSolution_le_exp_im φ z v t) (Real.exp_nonneg (-(|z.im| * t.val)))
    calc
      _ ≤ E*(‖v‖*Real.exp ((|z.im|+‖φ‖)*t.val)) := h
      _ = ‖v‖*Real.exp (‖φ‖*t.val) := by
        dsimp only [E]
        rw [mul_left_comm,← Real.exp_add]
        congr 2
        ring
      _ ≤ ‖v‖*Real.exp ‖φ‖ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [norm_nonneg φ,t.property.2])) (norm_nonneg _)
  have hR := classicalNormalizedRemainder_le_inverse_frequency φ hf hg hfi hgi z hz v t
  have h := mul_le_mul_of_nonneg_left (norm_deriv_classicalSolutionRemainder_le φ z v t) (Real.exp_nonneg (-(|z.im| * t.val)))
  calc
    _ ≤ E*(‖z‖*‖classicalSolutionRemainder φ z v t‖+‖φ‖*‖classicalSolution φ z v t‖) := h
    _ = ‖z‖*classicalNormalizedRemainder φ z v t+‖φ‖*(E*‖classicalSolution φ z v t‖) := by
      dsimp only [classicalNormalizedRemainder,E]
      ring
    _ ≤ ‖z‖*(classicalFirstBornUniformBudget φ*‖v‖/(2*‖z‖)*Real.exp ‖φ‖)+
        ‖φ‖*(‖v‖*Real.exp ‖φ‖) := add_le_add
      (mul_le_mul_of_nonneg_left hR (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hS (norm_nonneg _))
    _ = _ := by field_simp [norm_ne_zero_iff.mpr hz]

end NLS.ZakharovShabat
