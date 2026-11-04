import NLS.ComplexAnalysis.QuadraticCosinePrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Cubic primitive cancellation in cosine coordinates

The sine-weighted quadratic primitive vanishes at both endpoints.
Its cubic derivative therefore gives a zero weighted cosine integral,
without dividing by the sine or by the half-gap.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.ComplexAnalysis

/-- The squared quadratic cosine primitive annihilates its regular differential
numerator, including zero half-gaps and both angular endpoints. -/
theorem integral_quadraticCosinePrimitive_sq_mul_eq_zero
    (τ δ : ℂ) (H g : ℂ → ℂ)
    (hH : ∀ t : ℝ, DifferentiableAt ℂ H (cosineGapPoint τ δ (t:ℂ)))
    (heq : ∀ t : ℝ, quadraticRootPolynomial τ (δ^2) (cosineGapPoint τ δ (t:ℂ))*
      deriv H (cosineGapPoint τ δ (t:ℂ))+
        (cosineGapPoint τ δ (t:ℂ)-τ)*H (cosineGapPoint τ δ (t:ℂ)) =
          g (cosineGapPoint τ δ (t:ℂ)))
    (hg : Continuous (fun t : ℝ => g (cosineGapPoint τ δ (t:ℂ)))) :
    (∫ t in (0:ℝ)..Real.pi, (quadraticCosinePrimitive τ δ H (t:ℂ))^2*
      g (cosineGapPoint τ δ (t:ℂ))) = 0 := by
  let P : ℝ → ℂ := fun t => quadraticCosinePrimitive τ δ H (t:ℂ)
  have hd (t : ℝ) : HasDerivAt P (-I*g (cosineGapPoint τ δ (t:ℂ))) t :=
    (hasDerivAt_quadraticCosinePrimitive τ δ (t:ℂ) (g (cosineGapPoint τ δ (t:ℂ))) H
      (hH t) (heq t)).comp_ofReal
  have hP : Continuous P := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hprim (t : ℝ) : HasDerivAt (fun t => I*(P t)^3/3)
      ((P t)^2*g (cosineGapPoint τ δ (t:ℂ))) t := by
    have hh := (((hd t).pow 3).const_mul I).div_const (3:ℂ)
    have hv : I*((3:ℂ)*P t^2*(-I*g (cosineGapPoint τ δ (t:ℂ))))/3 =
        P t^2*g (cosineGapPoint τ δ (t:ℂ)) := by
      ring_nf
      simp only [I_sq,neg_mul,neg_neg,one_mul]
    simpa only [Nat.reduceSub,Nat.cast_ofNat,hv] using! hh
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hprim t)
    (((hP.pow 2).mul hg).intervalIntegrable 0 Real.pi)
  have h0 : P 0 = 0 := by simp only [P,quadraticCosinePrimitive,ofReal_zero,sin_zero,mul_zero,zero_mul]
  have hπ : P Real.pi = 0 := by
    simp only [P,quadraticCosinePrimitive,← Complex.ofReal_sin,Real.sin_pi,ofReal_zero,mul_zero,zero_mul]
  simpa only [h0,hπ,zero_pow (by decide : (3:ℕ)≠0),mul_zero,zero_div,sub_zero] using h

end NLS.ComplexAnalysis
