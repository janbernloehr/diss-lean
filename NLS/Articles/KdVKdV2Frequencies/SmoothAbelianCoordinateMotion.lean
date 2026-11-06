import NLS.Articles.KdVKdV2Frequencies.SmoothAbelianAngleMotion
import NLS.KdV.HillDirichletVelocityFiniteGap

/-! # Actual coordinate jets of both printed PDE fields at every gap

The derivatives of every physical matching coordinate extension are limits
of the actual Dirichlet spectral sums. At finite-gap sources these reduce
to finite sums, with no unproved Hamiltonian frequency evaluation.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.KdV
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies

theorem fderiv_hillDirichletAbelianCoordinate_both_pde
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0) (n : ℕ) (hn : 1≤n) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    ∀ (C : Coeff 2 → ℂ) (_hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q.val)),
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) →
      Tendsto (fun M : ℕ => (∑ j ∈ Finset.range M,
        hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
          (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))*
            kdvDirichletVelocityCoefficient Q q (j+1))*
              (I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn)) atTop (𝓝 ((fderiv ℂ C (SpectralWeight.one.toCoeff q.val))
          (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf))) ∧
      Tendsto (fun M : ℕ => (∑ j ∈ Finset.range M,
        hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
          (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))*
            kdv2DirichletVelocityCoefficient Q q (j+1))*
              (I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn)) atTop (𝓝 ((fderiv ℂ C (SpectralWeight.one.toCoeff q.val))
          (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf))) := by
  dsimp only
  intro C hC hmatch
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
    rw [map_zero]
    exact (Coeff.paritySubspace 0).zero_mem
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    rw [map_zero]
    intro k
    simp
  constructor
  · exact fderiv_hillDirichletAbelianCoordinate_velocity_extension q.val q.property.1 q.property.2 h0q h0r n hn C hC hmatch
      (kdvFourierDirection _ hf) (kdvDirichletVelocityCoefficient Q q)
      (fun k hk => hillDirichletVelocityData_kdv_coefficient Q hf hp hreal k hk)
  · exact fderiv_hillDirichletAbelianCoordinate_velocity_extension q.val q.property.1 q.property.2 h0q h0r n hn C hC hmatch
      (kdv2FourierDirection _ hf) (kdv2DirichletVelocityCoefficient Q q)
      (fun k hk => hillDirichletVelocityData_kdv2_coefficient Q hf hp hreal k hk)

theorem fderiv_hillDirichletAbelianCoordinate_closed_both_pde
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0) (n : ℕ) (hn : 1≤n) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    hillRealGapHalfLength q.val q.property.1 q.property.2 n=0 →
    ∀ (C : Coeff 2 → ℂ) (_hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q.val)),
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) →
      (fderiv ℂ C (SpectralWeight.one.toCoeff q.val))
          (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=0 ∧
      (fderiv ℂ C (SpectralWeight.one.toCoeff q.val))
          (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=0 := by
  dsimp only
  intro hc C hC hmatch
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
    rw [map_zero]
    exact (Coeff.paritySubspace 0).zero_mem
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    rw [map_zero]
    intro k
    simp
  constructor
  · exact fderiv_hillDirichletAbelianCoordinate_closed_velocity_extension_eq_zero q.val q.property.1 q.property.2 h0q h0r n hn hc C hC hmatch
      (kdvFourierDirection _ hf) (kdvDirichletVelocityCoefficient Q q n)
      (hillDirichletVelocityData_kdv_coefficient Q hf hp hreal n hn)
  · exact fderiv_hillDirichletAbelianCoordinate_closed_velocity_extension_eq_zero q.val q.property.1 q.property.2 h0q h0r n hn hc C hC hmatch
      (kdv2FourierDirection _ hf) (kdv2DirichletVelocityCoefficient Q q n)
      (hillDirichletVelocityData_kdv2_coefficient Q hf hp hreal n hn)

theorem fderiv_hillDirichletAbelianCoordinate_finite_gap_both_pde
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0) (n : ℕ) (hn : 1≤n) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    ∀ (N : ℕ),
      (∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q.val q.property.1 q.property.2 k=0) →
    ∀ (C : Coeff 2 → ℂ) (_hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q.val)),
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) →
      (fderiv ℂ C (SpectralWeight.one.toCoeff q.val))
          (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=
        (∑ j ∈ Finset.range N,
        hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
          (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))*
            kdvDirichletVelocityCoefficient Q q (j+1))*
              (I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn) ∧
      (fderiv ℂ C (SpectralWeight.one.toCoeff q.val))
          (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=
        (∑ j ∈ Finset.range N,
        hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
          (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))*
            kdv2DirichletVelocityCoefficient Q q (j+1))*
              (I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn) := by
  dsimp only
  intro N hclosed C hC hmatch
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
    rw [map_zero]
    exact (Coeff.paritySubspace 0).zero_mem
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    rw [map_zero]
    intro k
    simp
  constructor
  · exact fderiv_hillDirichletAbelianCoordinate_finite_gap_velocity q.val q.property.1 q.property.2 h0q h0r n hn C hC hmatch
      (kdvFourierDirection _ hf) (kdvDirichletVelocityCoefficient Q q)
      (fun k hk => hillDirichletVelocityData_kdv_coefficient Q hf hp hreal k hk) N hclosed
  · exact fderiv_hillDirichletAbelianCoordinate_finite_gap_velocity q.val q.property.1 q.property.2 h0q h0r n hn C hC hmatch
      (kdv2FourierDirection _ hf) (kdv2DirichletVelocityCoefficient Q q)
      (fun k hk => hillDirichletVelocityData_kdv2_coefficient Q hf hp hreal k hk) N hclosed

theorem exists_hillDirichletAbelianCoordinate_both_pde_extension
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0) (n : ℕ) (hn : 1≤n) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    ∃ Z : Coeff 2 → ℂ, AnalyticAt ℂ Z (SpectralWeight.one.toCoeff q.val) ∧
      Z (SpectralWeight.one.toCoeff q.val)=hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn ∧
      Tendsto (fun M : ℕ => (∑ j ∈ Finset.range M,
        hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
          (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))*
            kdvDirichletVelocityCoefficient Q q (j+1))*
              (I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn)) atTop (𝓝 ((fderiv ℂ Z (SpectralWeight.one.toCoeff q.val))
          (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf))) ∧
      Tendsto (fun M : ℕ => (∑ j ∈ Finset.range M,
        hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
          (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))*
            kdv2DirichletVelocityCoefficient Q q (j+1))*
              (I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn)) atTop (𝓝 ((fderiv ℂ Z (SpectralWeight.one.toCoeff q.val))
          (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf))) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        Z (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn := by
  dsimp only
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
    rw [map_zero]
    exact (Coeff.paritySubspace 0).zero_mem
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    rw [map_zero]
    intro k
    simp
  obtain ⟨Z,hZ,hZ0,_hclosed,hmatch⟩ :=
    exists_hillDirichletAbelianCoordinate_velocity_extension q.val q.property.1 q.property.2 h0q h0r n hn
  have hboth := fderiv_hillDirichletAbelianCoordinate_both_pde Q hf hp hreal n hn Z hZ.differentiableAt hmatch
  exact ⟨Z,hZ,hZ0,hboth.1,hboth.2,hmatch⟩

end NLS.Articles.KdVKdV2Frequencies
