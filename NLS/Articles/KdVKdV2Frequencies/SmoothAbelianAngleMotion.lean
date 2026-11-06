import NLS.Articles.KdVKdV2Frequencies.SmoothDirichletVelocityData
import NLS.KdV.HillDirichletVelocityAbelianAngle

/-! # Actual KdV and KdV2 derivatives of the physical Abelian angle

One analytic angle germ has its two physical PDE derivatives given by
convergent Dirichlet series. Only its own angle gap must be open.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.KdV
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies

def kdvDirichletVelocityCoefficient (Q : C(AddCircle (2:ℝ),ℂ))
    (q : RealPeriodOneHillPotential) (k : ℕ) : ℂ :=
  if hk : 1≤k then
    let μ : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 k hk
    (-2*(Q (0 : AddCircle (2:ℝ))+2*μ)/deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)) μ)
  else 0

theorem hillDirichletVelocityData_kdv_coefficient
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0) (k : ℕ) (hk : 1≤k) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    HillDirichletVelocityData q k hk
      (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)
      (kdvDirichletVelocityCoefficient Q q k) := by
  simpa only [kdvDirichletVelocityCoefficient,dif_pos hk] using
    hillDirichletVelocityData_kdv_pde Q hf hp hreal k hk

def kdv2DirichletVelocityCoefficient (Q : C(AddCircle (2:ℝ),ℂ))
    (q : RealPeriodOneHillPotential) (k : ℕ) : ℂ :=
  if hk : 1≤k then
    let μ : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 k hk
    (-2*(-iteratedDeriv 2 (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0+3*Q (0 : AddCircle (2:ℝ))^2+4*μ*Q (0 : AddCircle (2:ℝ))+8*μ^2)/deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)) μ)
  else 0

theorem hillDirichletVelocityData_kdv2_coefficient
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0) (k : ℕ) (hk : 1≤k) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    HillDirichletVelocityData q k hk
      (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)
      (kdv2DirichletVelocityCoefficient Q q k) := by
  simpa only [kdv2DirichletVelocityCoefficient,dif_pos hk] using
    hillDirichletVelocityData_kdv2_pde Q hf hp hreal k hk

theorem exists_hillDirichletAbelianAngle_both_pde_variation
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0) (n : ℕ) (hn : 1≤n) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    ∀ (_hnopen : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0),
    ∃ A ε : Coeff 2 → ℂ, ∃ e : ℂ,
      AnalyticAt ℂ A (SpectralWeight.one.toCoeff q.val) ∧
      AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q.val) ∧
      ε (SpectralWeight.one.toCoeff q.val)=e ∧ e∈segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ) ∧
      Tendsto (fun M : ℕ => ∑ j ∈ Finset.range M,
        hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
          (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))*
            kdvDirichletVelocityCoefficient Q q (j+1))
        atTop (𝓝 ((fderiv ℂ A (SpectralWeight.one.toCoeff q.val))
          (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf))) ∧
      Tendsto (fun M : ℕ => ∑ j ∈ Finset.range M,
        hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
          (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))*
            kdv2DirichletVelocityCoefficient Q q (j+1))
        atTop (𝓝 ((fderiv ℂ A (SpectralWeight.one.toCoeff q.val))
          (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf))) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0 ∧
        (ε (SpectralWeight.one.toCoeff p.val)).im=0 ∧
        cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 n)
          (hillRealGapHalfLength p.val p.property.1 p.property.2 n) (ε (SpectralWeight.one.toCoeff p.val))=
            (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ) ∧
        Complex.sin (ε (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 n hn ∧
        A (SpectralWeight.one.toCoeff p.val)=ε (SpectralWeight.one.toCoeff p.val)-(Real.pi:ℂ)+
          hillSummedRegularAbelianCorrection p.val p.property.1 p.property.2 n hn ∧
        (A (SpectralWeight.one.toCoeff p.val)).im=0 := by
  dsimp only
  intro hnopen
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
    rw [map_zero]
    exact (Coeff.paritySubspace 0).zero_mem
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    rw [map_zero]
    intro k
    simp
  obtain ⟨A,ε,e,hA,hε,hε0,he,hD,hphysical⟩ :=
    exists_hillDirichletAbelianAngle_velocity_variation q.val q.property.1 q.property.2 h0q h0r n hn hnopen
  exact ⟨A,ε,e,hA,hε,hε0,he,
    hD _ (kdvDirichletVelocityCoefficient Q q) (fun k hk => hillDirichletVelocityData_kdv_coefficient Q hf hp hreal k hk),
    hD _ (kdv2DirichletVelocityCoefficient Q q) (fun k hk => hillDirichletVelocityData_kdv2_coefficient Q hf hp hreal k hk),hphysical⟩

end NLS.Articles.KdVKdV2Frequencies
