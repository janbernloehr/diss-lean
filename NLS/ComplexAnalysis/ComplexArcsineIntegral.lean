import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-!
# Complex arcsine-weighted integrals

The substitution t=cos θ identifies the singular endpoint weight with
an ordinary cosine integral. The change-of-variables theorem applies to
complex values directly, and the integrability assertion is separate.
-/

noncomputable section
open Set MeasureTheory Real intervalIntegral
namespace NLS.ComplexAnalysis

/-- The literal inverse-square-root weighted complex integral. -/
theorem integral_div_sqrt_one_sub_sq_eq_cosine (f : ℝ → ℂ) :
    (∫ t in (-1:ℝ)..1, f t/(Real.sqrt (1-t^2):ℂ)) =
      ∫ θ in (0:ℝ)..Real.pi, f (Real.cos θ) := by
  calc
    _ = ∫ t in (1:ℝ)..(-1), -(1/Real.sqrt (1-t^2)) • f t := by
      rw [integral_symm,← intervalIntegral.integral_neg]
      apply integral_congr
      intro t _
      simp [Complex.real_smul,div_eq_mul_inv,mul_comm]
    _ = ∫ θ in Real.arccos 1..Real.arccos (-1), f (Real.cos θ) := by
      rw [← integral_deriv_smul_comp_of_deriv_nonpos
        (f' := fun t => -(1/Real.sqrt (1-t^2)))]
      · apply integral_congr
        intro t ht
        simp only [Function.comp_apply]
        rw [Real.cos_arccos (by aesop) (by aesop)]
      · fun_prop
      · exact fun t ht => Real.hasDerivAt_arccos (by aesop) (by aesop)
      · intro t _; exact neg_nonpos.mpr (one_div_nonneg.mpr (Real.sqrt_nonneg _))
    _ = _ := by simp

/-- A continuous numerator gives a genuinely integrable endpoint singularity. -/
theorem intervalIntegrable_div_sqrt_one_sub_sq {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1) 1)) :
    IntervalIntegrable (fun t => f t/(Real.sqrt (1-t^2):ℂ)) volume (-1) 1 := by
  have h := Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv.smul_continuousOn
    (show ContinuousOn f (uIcc (-1) 1) from by simpa only [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hf)
  simpa [Complex.real_smul,div_eq_mul_inv,mul_comm] using h

end NLS.ComplexAnalysis
