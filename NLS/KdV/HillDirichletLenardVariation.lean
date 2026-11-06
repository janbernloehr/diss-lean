import NLS.KdV.ClassicalHillDirichletLenard
import NLS.KdV.HillPolynomialDirections
import NLS.KdV.HillDirichletGradients
import NLS.KdV.HillDirichletSheetRoot

/-! # Actual Dirichlet branch velocities for physical Lenard directions

Physical Fourier reconstruction, the verified branch gradient and actual
mass normalization determine the sheet-oriented source velocity.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory MvPolynomial
open scoped ContDiff
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.DifferentialPolynomial
namespace NLS.KdV

theorem hillDirichlet_branch_fderiv_lenard_direction
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)),
      hillL2DirichletCharacteristic p (a p)=0) (P : DifferentialPolynomial.Polynomial) :
    let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
    let E := a q
    (fderiv ℂ a q) (hillPolynomialDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf (hillLenardPolynomial E P))=
      (-2*evaluate (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0 P 0*(hillL2DirichletSlope q E^2-1))/
        (scalarStateMass (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) : ℂ) := by
  dsimp only
  let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
  let E := a q
  let f := fun x : ℝ => Q (x : AddCircle (2:ℝ))
  change (fderiv ℂ a q) (hillPolynomialDirection f hf (hillLenardPolynomial E P))=_
  rw [hillDirichlet_branch_fderiv_integral q hr a ha hz]
  congr 1
  have hz0 : hillL2DirichletCharacteristic q E=0 := hz.self_of_nhds
  have hzC : (classicalHillFlow (scalarPotentialCurve f hf.continuous) E (0,1) 1).1=0 := by
    rw [hillL2DirichletCharacteristic_eq_classical] at hz0
    exact hz0
  have hi : (∫ x in (0:ℝ)..1,-(hillPhysicalDirection (hillPolynomialDirection f hf (hillLenardPolynomial E P))).ofLp.2 x*
      ((NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) x).1)^2)=
      ∫ x in (0:ℝ)..1,(classicalHillFlow (scalarPotentialCurve f hf.continuous) E (0,1) x).1^2*
        evaluate f 0 (hillLenardPolynomial E P) x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)]
    filter_upwards [hillPhysicalDirection_polynomialDirection f hf hp (hillLenardPolynomial E P),
      ae_restrict_mem measurableSet_Ioc] with x hx hxi
    rw [hx]
    have hx' : x∈Icc (0:ℝ) 1 := ⟨hxi.1.le,hxi.2⟩
    simp only [q,NLS.LinearVolterra.extend,projIcc_of_mem _ hx',hillL2FrequencyStateCurve_eq_classical,complex_sqrt_sq]
    exact mul_comm _ _
  rw [hi]
  change _= -2*evaluate f 0 P 0*(hillL2DirichletSlope q E^2-1)
  rw [hillL2DirichletSlope_eq_classical]
  exact integral_classicalHillDirichletSquare_lenard f hf hp E P hzC

theorem hillL2DirichletSlope_mul_sheetRoot_of_characteristic_zero
    (q : Coeff 2) (E : ℂ) (hz : hillL2DirichletCharacteristic q E=0) :
    hillL2DirichletSlope q E*hillDirichletSheetRoot q E=hillL2DirichletSlope q E^2-1 := by
  let z := Complex.sqrt E
  let t : Icc (0:ℝ) 1 := ⟨1,by norm_num⟩
  let c := (hillL2FrequencyStateCurve q z (1,0) t).1
  let d := hillL2DirichletSlope q E
  have hb : (hillL2FrequencyStateCurve q z (0,1) t).1=0 := hz
  have hw := hillL2FrequencyStateCurve_wronskian q z t
  rw [hb,zero_mul,sub_zero] at hw
  have hprod : c*d=1 := hw
  have htrace : c+d=hillL2Discriminant q E := by
    have ht := hillL2FrequencyStateCurve_trace q z
    rw [← hillL2Discriminant_sq,complex_sqrt_sq E] at ht
    exact ht
  unfold hillDirichletSheetRoot
  rw [← htrace]
  change d*(2*d-(c+d))=d^2-1
  linear_combination -hprod


/-- Mass normalization gives the signed sheet velocity without dividing by the sheet value. -/
theorem hillDirichlet_branch_fderiv_lenard_sheet_velocity
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)),
      hillL2DirichletCharacteristic p (a p)=0) (P : DifferentialPolynomial.Polynomial) :
    let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
    let E := a q
    (fderiv ℂ a q) (hillPolynomialDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf (hillLenardPolynomial E P))=
      hillDirichletSheetRoot q E*
        (-2*evaluate (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0 P 0/deriv (hillL2DirichletCharacteristic q) E) := by
  dsimp only
  let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
  let E := a q
  have hz0 : hillL2DirichletCharacteristic q E=0 := hz.self_of_nhds
  have hβ : hillL2DirichletSlope q E≠0 := hillL2DirichletSlope_ne_zero_at_dirichlet_zero q hr E hz0
  have hd : deriv (hillL2DirichletCharacteristic q) E≠0 :=
    hillL2DirichletCharacteristic_deriv_ne_zero q hr E hz0
  have hm := hillL2Dirichlet_derivative_normalization q hr E hz0
  change deriv (hillL2DirichletCharacteristic q) E*hillL2DirichletSlope q E=
    (scalarStateMass (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) : ℂ) at hm
  rw [hillDirichlet_branch_fderiv_lenard_direction Q hf hp hr a ha hz P]
  change (-2*evaluate (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0 P 0*(hillL2DirichletSlope q E^2-1))/_=
    hillDirichletSheetRoot q E*(-2*evaluate (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0 P 0/deriv (hillL2DirichletCharacteristic q) E)
  rw [← hm,← hillL2DirichletSlope_mul_sheetRoot_of_characteristic_zero q E hz0]
  field_simp [hβ,hd]

end NLS.KdV
