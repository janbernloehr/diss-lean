import NLS.KdV.ClassicalHillLenardIdentity
import NLS.KdV.HillPhysicalGradientPairing
import NLS.Fourier.UnitCurveConjugation

/-! # Actual Fourier directions of smooth periodic differential polynomials

The direction uses the bounded physical unit-interval Fourier analysis
and canonical even insertion. Its actual trace derivative is the scalar
Hill kernel pairing, so every Lenard direction annihilates that trace.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open scoped ContDiff
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.DifferentialPolynomial NLS.Fourier NLS.FunctionalAnalysis
namespace NLS.KdV

/-- Restrict the actual evaluated differential polynomial to one period. -/
def hillPolynomialCurve (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (P : DifferentialPolynomial.Polynomial) : Curve ℂ :=
  scalarPotentialCurve (evaluate f 0 P) (continuous_evaluate f 0 hf contDiff_const P)

/-- The actual physical Fourier tangent of the evaluated polynomial. -/
def hillPolynomialDirection (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (P : DifferentialPolynomial.Polynomial) : Coeff 2 :=
  Coeff.periodDouble (unitCurveCoefficientsCLM (hillPolynomialCurve f hf P))

theorem hillPolynomialDirection_mem_parity (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (P : DifferentialPolynomial.Polynomial) :
    hillPolynomialDirection f hf P∈Coeff.paritySubspace 0 := Coeff.periodDouble_mem _

theorem hillPolynomialCurve_endpoints (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (P : DifferentialPolynomial.Polynomial) :
    NLS.LinearVolterra.extend (hillPolynomialCurve f hf P) 0=NLS.LinearVolterra.extend (hillPolynomialCurve f hf P) 1 := by
  have he := periodic_evaluate f 0 1 hp (fun _ => rfl) P 0
  simpa [hillPolynomialCurve,scalarPotentialCurve,NLS.LinearVolterra.extend] using he.symm

/-- The direction is realized by the literal evaluated physical function. -/
theorem hillPhysicalDirection_polynomialDirection (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f 1) (P : DifferentialPolynomial.Polynomial) :
    (fun x => -(hillPhysicalDirection (hillPolynomialDirection f hf P)).ofLp.2 x)
      =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] evaluate f 0 P := by
  have he := hillPhysicalDirection_unitCurveCoefficients (hillPolynomialCurve f hf P)
    (hillPolynomialCurve_endpoints f hf hp P)
  filter_upwards [he,ae_restrict_mem measurableSet_Ioc] with x hx hxi
  change -(hillPhysicalDirection (Coeff.periodDouble (unitCurveCoefficientsCLM (hillPolynomialCurve f hf P)))).ofLp.2 x=_
  rw [hx]
  have hmem : x∈Icc (0:ℝ) 1 := ⟨hxi.1.le,hxi.2⟩
  simp only [hillPolynomialCurve,scalarPotentialCurve,NLS.LinearVolterra.extend,projIcc_of_mem _ hmem]
  rfl

/-- The zero Fourier mode is the actual period integral of the field. -/
theorem hillPolynomialDirection_zero (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (P : DifferentialPolynomial.Polynomial) :
    hillPolynomialDirection f hf P 0=∫ x in (0:ℝ)..1,evaluate f 0 P x := by
  change Coeff.periodDouble (unitCurveCoefficientsCLM (hillPolynomialCurve f hf P)) (2*0)=_
  rw [Coeff.periodDouble_even,unitCurveCoefficientsCLM_apply,unitCurveCoefficients_apply]
  simp only [periodOneCoefficient,← unitFourierCoefficient_eq_fourierCoeffOn,
    unitFourierCoefficient,mul_zero,neg_zero,wave_zero,mul_one]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hx
  simp only [hillPolynomialCurve,scalarPotentialCurve,NLS.LinearVolterra.extend,projIcc_of_mem _ hx']
  rfl

/-- A real evaluated physical field gives actual conjugate Fourier symmetry. -/
theorem hillPolynomialDirection_isReal (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (P : DifferentialPolynomial.Polynomial) (hreal : ∀ x : ℝ, (evaluate f 0 P x).im=0) :
    IsRealHillPotential (hillPolynomialDirection f hf P) := by
  have hs : star (hillPolynomialCurve f hf P)=hillPolynomialCurve f hf P := by
    ext t
    change star (evaluate f 0 P t)=evaluate f 0 P t
    apply Complex.ext <;> simp [hreal t]
  have he := periodDouble_unitCurveCoefficientsCLM_star (hillPolynomialCurve f hf P)
  rw [hs] at he
  intro k
  have hk := congrArg (fun a : Coeff 2 => a (-k)) he
  simpa only [hillPolynomialDirection,lp.star_apply,Coeff.reflection_apply,neg_neg,starRingEnd_apply] using hk

/-- The actual L2 Hill trace derivative along an actual smooth polynomial
field equals the literal scalar-kernel integral. -/
theorem fderiv_hillL2Discriminant_polynomialDirection
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (P : DifferentialPolynomial.Polynomial) (E : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E)
      (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
      (hillPolynomialDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf P)=
      ∫ x in (0:ℝ)..1,classicalHillTracePairingKernel (hillUnitPotentialCurve Q) E x*
        evaluate (fun y : ℝ => Q (y : AddCircle (2:ℝ))) 0 P x := by
  rw [hillPolynomialDirection,fderiv_hillL2Discriminant_unitCurveCoefficients _ _ _
    (hillPolynomialCurve_endpoints _ hf hp P),unitComplexCurveIntegral_apply]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hx
  simp only [ContinuousMap.mul_apply,NLS.LinearVolterra.extend,projIcc_of_mem _ hx',
    hillL2TraceGradientCurve_eq_classical,complex_sqrt_sq,hillPolynomialCurve,scalarPotentialCurve]
  exact mul_comm _ _

/-- The actual physical L2 trace annihilates every evaluated Lenard
polynomial direction at its spectral parameter. -/
theorem fderiv_hillL2Discriminant_lenardDirection_eq_zero
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (P : DifferentialPolynomial.Polynomial) (E : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E)
      (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
      (hillPolynomialDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf (hillLenardPolynomial E P))=0 := by
  rw [fderiv_hillL2Discriminant_polynomialDirection Q hf hp]
  exact integral_classicalHillTracePairingKernel_lenard_eq_zero _ hf hp E P

end NLS.KdV
