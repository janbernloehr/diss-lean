import NLS.Articles.KdVKdV2Frequencies.SmoothSpectralStationarity
import NLS.KdV.HillDirichletLenardSheetVariation

/-! # Actual Dirichlet velocities of the printed KdV and KdV2 fields

Every analytic physical Dirichlet branch has the stated source velocity.
The formulas retain actual mass and sheet normalization at closed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory MvPolynomial
open scoped ContDiff
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.DifferentialPolynomial
open NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies

theorem hillDirichlet_branch_fderiv_kdv_direction
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)),
      hillL2DirichletCharacteristic p (a p)=0) :
    let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
    let E := a q
    (fderiv ℂ a q) (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=
      (-2*(Q (0 : AddCircle (2:ℝ))+2*E)*(hillL2DirichletSlope q E^2-1))/
        (scalarStateMass (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) : ℂ) := by
  have hd := hillDirichlet_branch_fderiv_lenard_direction Q hf hp hr a ha hz
    (kdvLenardSeed (a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))))
  dsimp only at hd ⊢
  rw [hillLenardPolynomial_kdvLenardSeed] at hd
  simpa [kdvFourierDirection,kdvLenardSeed,scalarJet,evaluate] using hd

theorem hillDirichlet_branch_fderiv_kdv2_direction
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)),
      hillL2DirichletCharacteristic p (a p)=0) :
    let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
    let E := a q
    let f := fun x : ℝ => Q (x : AddCircle (2:ℝ))
    (fderiv ℂ a q) (kdv2FourierDirection f hf)=
      (-2*(-iteratedDeriv 2 f 0+3*f 0^2+4*E*f 0+8*E^2)*(hillL2DirichletSlope q E^2-1))/
        (scalarStateMass (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) : ℂ) := by
  have hd := hillDirichlet_branch_fderiv_lenard_direction Q hf hp hr a ha hz
    (kdv2LenardSeed (a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))))
  dsimp only at hd ⊢
  rw [hillLenardPolynomial_kdv2LenardSeed] at hd
  simpa [kdv2FourierDirection,kdv2LenardSeed,kdvGradient,scalarJet,evaluate] using hd


/-- The actual PDE branch velocity in signed sheet normalization, including closed gaps. -/
theorem hillDirichlet_branch_fderiv_kdv_sheet_velocity
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)),
      hillL2DirichletCharacteristic p (a p)=0) :
    let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
    let E := a q
    (fderiv ℂ a q) (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=
      hillDirichletSheetRoot q E*(-2*(Q (0 : AddCircle (2:ℝ))+2*E)/deriv (hillL2DirichletCharacteristic q) E) := by
  have hd := hillDirichlet_branch_fderiv_lenard_sheet_velocity Q hf hp hr a ha hz
    (kdvLenardSeed (a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))))
  dsimp only at hd ⊢
  rw [hillLenardPolynomial_kdvLenardSeed] at hd
  simpa [kdvFourierDirection,kdvLenardSeed,scalarJet,evaluate] using hd

/-- The actual PDE branch velocity in signed sheet normalization, including closed gaps. -/
theorem hillDirichlet_branch_fderiv_kdv2_sheet_velocity
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)),
      hillL2DirichletCharacteristic p (a p)=0) :
    let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
    let E := a q
    let f := fun x : ℝ => Q (x : AddCircle (2:ℝ))
    (fderiv ℂ a q) (kdv2FourierDirection f hf)=
      hillDirichletSheetRoot q E*(-2*(-iteratedDeriv 2 f 0+3*f 0^2+4*E*f 0+8*E^2)/deriv (hillL2DirichletCharacteristic q) E) := by
  have hd := hillDirichlet_branch_fderiv_lenard_sheet_velocity Q hf hp hr a ha hz
    (kdv2LenardSeed (a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))))
  dsimp only at hd ⊢
  rw [hillLenardPolynomial_kdv2LenardSeed] at hd
  simpa [kdv2FourierDirection,kdv2LenardSeed,kdvGradient,scalarJet,evaluate] using hd


/-- The genuine moving signed sheet velocity, including terminal band edges. -/
theorem hillDirichletSheetRoot_moving_kdv_velocity
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)),
      hillL2DirichletCharacteristic p (a p)=0) :
    let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
    let E := a q
    (fderiv ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p (a p)) q) (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=
      (hillL2Discriminant q E*deriv (hillL2Discriminant q) E)*(-2*(Q (0 : AddCircle (2:ℝ))+2*E)/deriv (hillL2DirichletCharacteristic q) E) := by
  have hd := hillDirichletSheetRoot_moving_lenard_velocity Q hf hp hr a ha hz
    (kdvLenardSeed (a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))))
  dsimp only at hd ⊢
  rw [hillLenardPolynomial_kdvLenardSeed] at hd
  simpa [kdvFourierDirection,kdvLenardSeed,scalarJet,evaluate] using hd

/-- The genuine moving signed sheet velocity, including terminal band edges. -/
theorem hillDirichletSheetRoot_moving_kdv2_velocity
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)),
      hillL2DirichletCharacteristic p (a p)=0) :
    let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
    let E := a q
    let f := fun x : ℝ => Q (x : AddCircle (2:ℝ))
    (fderiv ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p (a p)) q) (kdv2FourierDirection f hf)=
      (hillL2Discriminant q E*deriv (hillL2Discriminant q) E)*(-2*(-iteratedDeriv 2 f 0+3*f 0^2+4*E*f 0+8*E^2)/deriv (hillL2DirichletCharacteristic q) E) := by
  have hd := hillDirichletSheetRoot_moving_lenard_velocity Q hf hp hr a ha hz
    (kdv2LenardSeed (a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))))
  dsimp only at hd ⊢
  rw [hillLenardPolynomial_kdv2LenardSeed] at hd
  simpa [kdv2FourierDirection,kdv2LenardSeed,kdvGradient,scalarJet,evaluate] using hd

end NLS.Articles.KdVKdV2Frequencies
