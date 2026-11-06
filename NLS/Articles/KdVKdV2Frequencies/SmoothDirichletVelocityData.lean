import NLS.KdV.HillDirichletVelocityData
import NLS.Articles.KdVKdV2Frequencies.SmoothDirichletMotion

/-! # Proved Dirichlet first-variation data for both physical PDE fields -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.KdV
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies

theorem hillDirichletVelocityData_kdv_pde
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0) (k : ℕ) (hk : 1≤k) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    let μ : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 k hk
    HillDirichletVelocityData q k hk
      (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)
      (-2*(Q (0 : AddCircle (2:ℝ))+2*μ)/deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)) μ) := by
  dsimp only
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  let μ : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 k hk
  let K : ℂ := -2*(Q (0 : AddCircle (2:ℝ))+2*μ)/deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)) μ
  refine ⟨hillPolynomialDirection_mem_parity _ hf kdvVectorField,
    (fun z => fderiv_hillL2Discriminant_kdvFourierDirection_eq_zero Q hf hp z),?_,?_⟩
  · intro a ha ha0 haz
    change AnalyticAt ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) at ha
    change a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))=μ at ha0
    change (∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)), hillL2DirichletCharacteristic p (a p)=0) at haz
    change (fderiv ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
      (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))
        (a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))*K
    rw [ha0]
    have hm := NLS.Articles.KdVKdV2Frequencies.hillDirichlet_branch_fderiv_kdv_sheet_velocity
      Q hf hp (isRealHillPotential_hillContinuousCoefficients Q hreal) a ha haz
    dsimp only at hm
    rw [ha0] at hm
    exact hm
  · intro a ha ha0 haz
    change AnalyticAt ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) at ha
    change a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))=μ at ha0
    change (∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)), hillL2DirichletCharacteristic p (a p)=0) at haz
    change (fderiv ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p (a p))
      (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
      (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=
      (hillL2Discriminant (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))
        (a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))*
      deriv (hillL2Discriminant (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
        (a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))))*K
    rw [ha0]
    have hs := NLS.Articles.KdVKdV2Frequencies.hillDirichletSheetRoot_moving_kdv_velocity
      Q hf hp (isRealHillPotential_hillContinuousCoefficients Q hreal) a ha haz
    dsimp only at hs
    rw [ha0] at hs
    exact hs

theorem hillDirichletVelocityData_kdv2_pde
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0) (k : ℕ) (hk : 1≤k) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    let μ : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 k hk
    HillDirichletVelocityData q k hk
      (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)
      (-2*(-iteratedDeriv 2 (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0+3*Q (0 : AddCircle (2:ℝ))^2+4*μ*Q (0 : AddCircle (2:ℝ))+8*μ^2)/deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)) μ) := by
  dsimp only
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  let μ : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 k hk
  let K : ℂ := -2*(-iteratedDeriv 2 (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0+3*Q (0 : AddCircle (2:ℝ))^2+4*μ*Q (0 : AddCircle (2:ℝ))+8*μ^2)/deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)) μ
  refine ⟨hillPolynomialDirection_mem_parity _ hf kdv2VectorField,
    (fun z => fderiv_hillL2Discriminant_kdv2FourierDirection_eq_zero Q hf hp z),?_,?_⟩
  · intro a ha ha0 haz
    change AnalyticAt ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) at ha
    change a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))=μ at ha0
    change (∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)), hillL2DirichletCharacteristic p (a p)=0) at haz
    change (fderiv ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
      (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))
        (a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))*K
    rw [ha0]
    have hm := NLS.Articles.KdVKdV2Frequencies.hillDirichlet_branch_fderiv_kdv2_sheet_velocity
      Q hf hp (isRealHillPotential_hillContinuousCoefficients Q hreal) a ha haz
    dsimp only at hm
    rw [ha0] at hm
    exact hm
  · intro a ha ha0 haz
    change AnalyticAt ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) at ha
    change a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))=μ at ha0
    change (∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)), hillL2DirichletCharacteristic p (a p)=0) at haz
    change (fderiv ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p (a p))
      (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
      (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=
      (hillL2Discriminant (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))
        (a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))*
      deriv (hillL2Discriminant (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
        (a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))))*K
    rw [ha0]
    have hs := NLS.Articles.KdVKdV2Frequencies.hillDirichletSheetRoot_moving_kdv2_velocity
      Q hf hp (isRealHillPotential_hillContinuousCoefficients Q hreal) a ha haz
    dsimp only at hs
    rw [ha0] at hs
    exact hs

end NLS.Articles.KdVKdV2Frequencies
