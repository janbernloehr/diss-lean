import NLS.ZakharovShabat.ClassicalScalarForcingDiagonalIdentity
import NLS.ZakharovShabat.SobolevWKBLeadingForcedComparison

/-! # The leading WKB diagonal primitive

The exact leading forced response splits off the primitive of the original Riccati density with its signed coefficient.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The exact leading forced response exposes its diagonal primitive with
the sign inherited from the original Riccati density convention. -/
theorem nlsWKBLeadingScalar_fst_integral_identity
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (N : ℕ) (z : ℂ) (t : Icc (0:ℝ) 1) :
    let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
    let Y := classicalForcedKernelSolution Φ
      (classicalScalarForcing (nlsWKBLeadingScalar a b N z)
        (continuous_nlsWKBLeadingScalar a b ha hb N z)) z
    (2*I*z)*(Y t).1 = I*a t*(Y t).2-
      exp (-I*z*t.val)*((∫ x in (0:ℝ)..t.val, exp (I*z*x)*
        (I*deriv a x*(Y x).2+a x*b x*(Y x).1))+
        ((2*I*z)⁻¹)^N*(∫ x in (0:ℝ)..t.val, a x*nlsRiccatiDensity a b N x)) := by
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  let Y := classicalForcedKernelSolution Φ
    (classicalScalarForcing (nlsWKBLeadingScalar a b N z)
      (continuous_nlsWKBLeadingScalar a b ha hb N z)) z
  have h := classicalScalarForcing_fst_integral_identity a b (nlsWKBLeadingScalar a b N z)
    (ha.of_le (by simp)) hb.continuous (continuous_nlsWKBLeadingScalar a b ha hb N z) z t
  change (2*I*z)*(Y t).1 = I*a t*(Y t).2-_
  change (2*I*z)*(Y t).1 = I*a t*(Y t).2-_ at h
  rw [h]
  congr 2
  change (∫ x in (0:ℝ)..t.val, exp (I*z*x)*
    (I*deriv a x*(Y x).2+a x*b x*(Y x).1+I*a x*nlsWKBLeadingScalar a b N z x)) = _
  have hY : Continuous Y := continuous_classicalForcedKernelSolution _ _ _
  have hda : Continuous (deriv a) := ha.continuous_deriv (by simp)
  have hr : Continuous (nlsRiccatiDensity a b N) := (contDiff_nlsRiccatiDensity a b ha hb N).continuous
  have he (x : ℝ) : exp (I*z*x)*
      (I*deriv a x*(Y x).2+a x*b x*(Y x).1+I*a x*nlsWKBLeadingScalar a b N z x) =
      exp (I*z*x)*(I*deriv a x*(Y x).2+a x*b x*(Y x).1)+
      ((2*I*z)⁻¹)^N*(a x*nlsRiccatiDensity a b N x) := by
    have hexp : exp (I*z*x)*exp (-I*z*x) = 1 := by rw [← exp_add]; ring_nf; simp
    dsimp only [nlsWKBLeadingScalar]
    linear_combination (norm := (ring_nf; simp [I_sq]))
      -I*I*a x*nlsRiccatiDensity a b N x*((2*I*z)⁻¹)^N*hexp
  simp_rw [he]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),intervalIntegral.integral_const_mul]

end NLS.ZakharovShabat
