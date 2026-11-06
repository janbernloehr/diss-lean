import NLS.Articles.KdVKdV2Frequencies.SmoothKdVIdentities
import NLS.KdV.HillPolynomialDirections
import NLS.KdV.HillSmoothPhysicalQuartic

/-! # Actual KdV and KdV2 directions preserve the Hill traces and actions

The physical right sides in (1) and (2) are evaluated differential
polynomials. Their Lenard seeds depend on the spectral parameter, but their
Fourier directions do not. The proved scalar trace-kernel concomitant
therefore gives exact trace and action source stationarity for each actual
PDE field, including at closed gaps. No flow or frequency identity is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory MvPolynomial
open scoped ContDiff
open NLS.KdV NLS.DifferentialPolynomial NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies

/-- The spectral seed whose Lenard expression is the actual cubic KdV field. -/
def kdvLenardSeed (E : ℂ) : DifferentialPolynomial.Polynomial := scalarJet 0+C (2*E)

/-- The spectral seed whose Lenard expression is the actual fifth-order field. -/
def kdv2LenardSeed (E : ℂ) : DifferentialPolynomial.Polynomial :=
  kdvGradient+C (4*E)*scalarJet 0+C (8*E^2)

theorem hillLenardPolynomial_kdvLenardSeed (E : ℂ) :
    hillLenardPolynomial E (kdvLenardSeed E)=kdvVectorField := by
  simp [hillLenardPolynomial,kdvLenardSeed,kdvVectorField,scalarJet,
    Function.iterate_succ_apply',Derivation.leibniz,nextJet,smul_eq_mul]
  norm_num only [map_ofNat]
  ring

theorem hillLenardPolynomial_kdv2LenardSeed (E : ℂ) :
    hillLenardPolynomial E (kdv2LenardSeed E)=kdv2VectorField := by
  simp [hillLenardPolynomial,kdv2LenardSeed,kdvGradient,kdv2VectorField,scalarJet,
    Function.iterate_succ_apply',Derivation.leibniz,nextJet,smul_eq_mul,nsmul_eq_mul]
  norm_num only [map_ofNat]
  ring

/-- The actual physical KdV right side realized in the original Fourier source. -/
def kdvFourierDirection (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) : Coeff 2 :=
  hillPolynomialDirection f hf kdvVectorField

/-- The actual physical KdV2 right side realized in the original Fourier source. -/
def kdv2FourierDirection (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) : Coeff 2 :=
  hillPolynomialDirection f hf kdv2VectorField

/-- Physical L2 reconstruction is the literal KdV right side almost everywhere. -/
theorem hillPhysicalDirection_kdvFourierDirection (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f 1) :
    (fun x => -(hillPhysicalDirection (kdvFourierDirection f hf)).ofLp.2 x)
      =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] kdvRHS f := by
  simpa only [kdvFourierDirection,show evaluate f 0 kdvVectorField=kdvRHS f from funext (evaluate_kdvVectorField f)] using
    hillPhysicalDirection_polynomialDirection f hf hp kdvVectorField

/-- Physical L2 reconstruction is the literal KdV2 right side almost everywhere. -/
theorem hillPhysicalDirection_kdv2FourierDirection (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f 1) :
    (fun x => -(hillPhysicalDirection (kdv2FourierDirection f hf)).ofLp.2 x)
      =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] kdv2RHS f := by
  simpa only [kdv2FourierDirection,show evaluate f 0 kdv2VectorField=kdv2RHS f from funext (evaluate_kdv2VectorField f)] using
    hillPhysicalDirection_polynomialDirection f hf hp kdv2VectorField

/-- The physical KdV Fourier velocity has zero mean. -/
theorem kdvFourierDirection_zero (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    kdvFourierDirection f hf 0=0 := by
  rw [kdvFourierDirection,hillPolynomialDirection_zero]
  simpa only [evaluate_kdvVectorField] using integral_kdvRHS_eq_zero f hf hp

/-- The physical KdV2 Fourier velocity has zero mean. -/
theorem kdv2FourierDirection_zero (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    kdv2FourierDirection f hf 0=0 := by
  rw [kdv2FourierDirection,hillPolynomialDirection_zero]
  simpa only [evaluate_kdv2VectorField] using integral_kdv2RHS_eq_zero f hf hp

private theorem iteratedDeriv_im_zero (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hreal : ∀ x : ℝ, (f x).im=0) (n : ℕ) (x : ℝ) : (iteratedDeriv n f x).im=0 := by
  induction n generalizing x with
  | zero => exact hreal x
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact deriv_im_eq_zero_of_real _
      ((NLS.FunctionalAnalysis.contDiff_iteratedDeriv f hf n).differentiable (by simp)) ih x

/-- Real physical potentials produce real physical KdV Fourier velocities. -/
theorem kdvFourierDirection_isReal (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hreal : ∀ x : ℝ, (f x).im=0) : IsRealHillPotential (kdvFourierDirection f hf) := by
  apply hillPolynomialDirection_isReal
  intro x
  rw [evaluate_kdvVectorField]
  have hd := deriv_im_eq_zero_of_real f (hf.differentiable (by simp)) hreal x
  simp [kdvRHS,mul_im,hreal x,iteratedDeriv_im_zero f hf hreal,hd]

/-- Real physical potentials produce real physical KdV2 Fourier velocities. -/
theorem kdv2FourierDirection_isReal (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hreal : ∀ x : ℝ, (f x).im=0) : IsRealHillPotential (kdv2FourierDirection f hf) := by
  apply hillPolynomialDirection_isReal
  intro x
  rw [evaluate_kdv2VectorField]
  have hd := deriv_im_eq_zero_of_real f (hf.differentiable (by simp)) hreal x
  simp [kdv2RHS,mul_im,pow_two,hreal x,iteratedDeriv_im_zero f hf hreal,hd]

variable (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)

include hp

/-- The actual physical KdV direction annihilates every actual L2 Hill trace. -/
theorem fderiv_hillL2Discriminant_kdvFourierDirection_eq_zero (E : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E)
      (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
      (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=0 := by
  have hd := fderiv_hillL2Discriminant_lenardDirection_eq_zero Q hf hp (kdvLenardSeed E) E
  rw [hillLenardPolynomial_kdvLenardSeed] at hd
  exact hd

/-- The actual physical KdV2 direction annihilates every actual L2 Hill trace. -/
theorem fderiv_hillL2Discriminant_kdv2FourierDirection_eq_zero (E : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E)
      (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
      (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=0 := by
  have hd := fderiv_hillL2Discriminant_lenardDirection_eq_zero Q hf hp (kdv2LenardSeed E) E
  rw [hillLenardPolynomial_kdv2LenardSeed] at hd
  exact hd

variable (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)

/-- Every matching differentiable physical action extension is stationary
along the literal KdV field, including at any closed selected gap. -/
theorem fderiv_hillRealAction_kdvFourierDirection_eq_zero
    (n : ℕ) (hn : 1≤n) (A : Coeff 2 → ℂ)
    (hA : DifferentiableAt ℂ A (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝
      (⟨hillContinuousCoefficients Q,hillContinuousCoefficients_mem_even Q hp,
        isRealHillPotential_hillContinuousCoefficients Q hreal⟩ : RealPeriodOneHillPotential),
      A (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 n 0:ℂ)) :
    (fderiv ℂ A (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
      (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=0 := by
  rw [fderiv_hillRealGapAction_extension_apply (hillContinuousCoefficients Q)
    (hillContinuousCoefficients_mem_even Q hp) (isRealHillPotential_hillContinuousCoefficients Q hreal)
    n hn A hA hmatch (kdvFourierDirection _ hf) (hillPolynomialDirection_mem_parity _ hf kdvVectorField)]
  simp only [fderiv_hillL2Discriminant_kdvFourierDirection_eq_zero Q hf hp,zero_div]
  simp [circleIntegral]

/-- Every matching differentiable physical action extension is stationary
along the literal KdV2 field, including at any closed selected gap. -/
theorem fderiv_hillRealAction_kdv2FourierDirection_eq_zero
    (n : ℕ) (hn : 1≤n) (A : Coeff 2 → ℂ)
    (hA : DifferentiableAt ℂ A (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝
      (⟨hillContinuousCoefficients Q,hillContinuousCoefficients_mem_even Q hp,
        isRealHillPotential_hillContinuousCoefficients Q hreal⟩ : RealPeriodOneHillPotential),
      A (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 n 0:ℂ)) :
    (fderiv ℂ A (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
      (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=0 := by
  rw [fderiv_hillRealGapAction_extension_apply (hillContinuousCoefficients Q)
    (hillContinuousCoefficients_mem_even Q hp) (isRealHillPotential_hillContinuousCoefficients Q hreal)
    n hn A hA hmatch (kdv2FourierDirection _ hf) (hillPolynomialDirection_mem_parity _ hf kdv2VectorField)]
  simp only [fderiv_hillL2Discriminant_kdv2FourierDirection_eq_zero Q hf hp,zero_div]
  simp [circleIntegral]

end NLS.Articles.KdVKdV2Frequencies
