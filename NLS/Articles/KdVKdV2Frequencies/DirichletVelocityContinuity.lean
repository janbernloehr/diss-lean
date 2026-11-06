import NLS.Articles.KdVKdV2Frequencies.FiniteGapDirichletVelocityContours
import NLS.KdV.HillGlobalDifferentialContinuity
import NLS.KdV.HillDirichletDerivativeContinuity

/-! # Continuity of actual finite Dirichlet velocity sums at all real gaps -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies

/-- Actual KdV residue coefficients are continuous even when gaps collapse. -/
theorem continuous_kdvDirichletVelocityCoefficient_family {T : Type*} [TopologicalSpace T]
    (Q : T → C(AddCircle (2 : ℝ),ℂ)) (hQ : Continuous Q)
    (p : T → RealPeriodOneHillPotential) (hp : Continuous p) (k : ℕ) :
    Continuous (fun x => kdvDirichletVelocityCoefficient (Q x) (p x) k) := by
  by_cases hk : 1≤k
  · have hμ : Continuous (fun x => (hillDirichletEnergy (p x).val (p x).property.1 (p x).property.2 k hk : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_hillDirichletEnergy k hk).comp hp)
    have hq0 : Continuous (fun x => Q x (0 : AddCircle (2 : ℝ))) := (continuous_eval_const _).comp hQ
    have hden := (continuous_hillDirichletCharacteristic_deriv_at_label k hk).comp hp
    have hnum : Continuous (fun x => (-2 : ℂ)*(Q x 0+2*(hillDirichletEnergy (p x).val (p x).property.1 (p x).property.2 k hk : ℂ))) := by
      fun_prop
    simpa only [kdvDirichletVelocityCoefficient,dif_pos hk,Pi.div_apply,Function.comp_def] using! hnum.div hden (fun x =>
      hillL2DirichletCharacteristic_deriv_ne_zero _ (p x).property.2 _
        (hillDirichletEnergy_zero (p x).val (p x).property.1 (p x).property.2 k hk))
  · simpa only [kdvDirichletVelocityCoefficient,dif_neg hk] using (continuous_const (X := T) (y := (0 : ℂ)))

/-- The physical KdV2 residue coefficients are continuous whenever the
actual second spatial jet at zero is continuous, including every closed gap. -/
theorem continuous_kdv2DirichletVelocityCoefficient_family {T : Type*} [TopologicalSpace T]
    (Q : T → C(AddCircle (2 : ℝ),ℂ)) (hQ : Continuous Q)
    (hD : Continuous (fun x => iteratedDeriv 2 (fun y : ℝ => Q x (y : AddCircle (2 : ℝ))) 0))
    (p : T → RealPeriodOneHillPotential) (hp : Continuous p) (k : ℕ) :
    Continuous (fun x => kdv2DirichletVelocityCoefficient (Q x) (p x) k) := by
  by_cases hk : 1≤k
  · have hμ : Continuous (fun x => (hillDirichletEnergy (p x).val (p x).property.1 (p x).property.2 k hk : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_hillDirichletEnergy k hk).comp hp)
    have hq0 : Continuous (fun x => Q x (0 : AddCircle (2 : ℝ))) := (continuous_eval_const _).comp hQ
    have hden := (continuous_hillDirichletCharacteristic_deriv_at_label k hk).comp hp
    have hnum : Continuous (fun x => (-2 : ℂ)*(-iteratedDeriv 2 (fun y : ℝ => Q x (y : AddCircle (2 : ℝ))) 0+
        3*Q x 0^2+4*(hillDirichletEnergy (p x).val (p x).property.1 (p x).property.2 k hk : ℂ)*Q x 0+
          8*(hillDirichletEnergy (p x).val (p x).property.1 (p x).property.2 k hk : ℂ)^2)) := by
      fun_prop
    simpa only [kdv2DirichletVelocityCoefficient,dif_pos hk,Pi.div_apply,Function.comp_def] using! hnum.div hden (fun x =>
      hillL2DirichletCharacteristic_deriv_ne_zero _ (p x).property.2 _
        (hillDirichletEnergy_zero (p x).val (p x).property.1 (p x).property.2 k hk))
  · simpa only [kdv2DirichletVelocityCoefficient,dif_neg hk] using (continuous_const (X := T) (y := (0 : ℂ)))

/-- The entire actual finite KdV spectral sum is continuous through closed own modes. -/
theorem continuous_kdvDirichletVelocitySum_family {T : Type*} [TopologicalSpace T]
    (Q : T → C(AddCircle (2 : ℝ),ℂ)) (hQ : Continuous Q)
    (p : T → RealPeriodOneHillPotential) (hp : Continuous p) (n : ℕ+) (N : ℕ) :
    Continuous (fun x => kdvDirichletVelocitySum (Q x) (p x) n n.pos N) := by
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
    rw [map_zero]
    exact (Coeff.paritySubspace 0).zero_mem
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    rw [map_zero]
    intro j
    simp
  apply continuous_finsetSum
  intro j _
  have hμ : Continuous (fun x => (hillDirichletEnergy (p x).val (p x).property.1 (p x).property.2 (j+1) (by omega) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_hillDirichletEnergy (j+1) (by omega)).comp hp)
  have hψ := (continuous_hillAbelianSelectedGlobalPsi_joint h0q h0r n n.pos).comp (hμ.prodMk hp)
  simpa only [Function.comp_def] using!
    hψ.mul (continuous_kdvDirichletVelocityCoefficient_family Q hQ p hp (j+1))

/-- The complete actual finite KdV2 spectral sum has the same continuity,
with its second physical jet hypothesis stated explicitly. -/
theorem continuous_kdv2DirichletVelocitySum_family {T : Type*} [TopologicalSpace T]
    (Q : T → C(AddCircle (2 : ℝ),ℂ)) (hQ : Continuous Q)
    (hD : Continuous (fun x => iteratedDeriv 2 (fun y : ℝ => Q x (y : AddCircle (2 : ℝ))) 0))
    (p : T → RealPeriodOneHillPotential) (hp : Continuous p) (n : ℕ+) (N : ℕ) :
    Continuous (fun x => kdv2DirichletVelocitySum (Q x) (p x) n n.pos N) := by
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
    rw [map_zero]
    exact (Coeff.paritySubspace 0).zero_mem
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    rw [map_zero]
    intro j
    simp
  apply continuous_finsetSum
  intro j _
  have hμ : Continuous (fun x => (hillDirichletEnergy (p x).val (p x).property.1 (p x).property.2 (j+1) (by omega) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_hillDirichletEnergy (j+1) (by omega)).comp hp)
  have hψ := (continuous_hillAbelianSelectedGlobalPsi_joint h0q h0r n n.pos).comp (hμ.prodMk hp)
  simpa only [Function.comp_def] using!
    hψ.mul (continuous_kdv2DirichletVelocityCoefficient_family Q hQ hD p hp (j+1))

end NLS.Articles.KdVKdV2Frequencies
