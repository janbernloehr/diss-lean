import NLS.KdV.HillFreeDirichlet
import NLS.KdV.HillL2StateCurve
import NLS.KdV.HillDirichletCosineData
import NLS.KdV.HillFreeAbelianNormalization

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

/-- The exact free cosine state, retaining its original value-one initial data. -/
theorem classicalHillFlow_free_cosine (z : ℂ) (t : Icc (0 : ℝ) 1) :
    classicalHillFlow 0 (z^2) (1,0) t = (cos (z*t.val),-z*sin (z*t.val)) := by
  apply Eq.symm
  apply solution_unique (classicalHillCoefficientCurve 0 (z^2)) (1,0)
    (fun x : ℝ => (cos (z*x),-z*sin (z*x))) (by fun_prop) (by simp) _ t.property
  intro s _
  have harg : HasDerivAt (fun w : ℂ => z*w) z (s.val : ℂ) := by
    convert! (hasDerivAt_id (s.val : ℂ)).const_mul z using 1
    ring
  have hh := harg.ccos.comp_ofReal.prodMk ((harg.csin.const_mul (-z)).comp_ofReal)
  change HasDerivAt (fun x : ℝ => (cos (z*x),-z*sin (z*x)))
    (-z*sin (z*s.val),(0-z^2)*cos (z*s.val)) s.val
  convert! hh using 1
  apply Prod.ext <;> dsimp <;> ring

private theorem zero_continuous_coefficients :
    SpectralWeight.one.toCoeff (hillContinuousCoefficients (0 : C(AddCircle (2 : ℝ),ℂ))) = (0 : Coeff 2) := by
  ext k
  simpa only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply,Fourier.continuousFourierCLM_apply] using
    congrArg (fun f : Coeff 2 => f k) (map_zero Fourier.continuousFourierCLM)

/-- The literal rough-state construction agrees with the free sine state. -/
theorem hillL2FrequencyStateCurve_free_sine (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    hillL2FrequencyStateCurve 0 z (0,1) t = (sin (z*t.val)/z,cos (z*t.val)) := by
  rw [←zero_continuous_coefficients,hillL2FrequencyStateCurve_eq_classical]
  have hQ : hillUnitPotentialCurve (0 : C(AddCircle (2 : ℝ),ℂ)) = 0 := by ext s; rfl
  rw [hQ,classicalHillFlow_free_sine z hz]

/-- The literal rough-state construction agrees with the free cosine state. -/
theorem hillL2FrequencyStateCurve_free_cosine (z : ℂ) (t : Icc (0 : ℝ) 1) :
    hillL2FrequencyStateCurve 0 z (1,0) t = (cos (z*t.val),-z*sin (z*t.val)) := by
  rw [←zero_continuous_coefficients,hillL2FrequencyStateCurve_eq_classical]
  have hQ : hillUnitPotentialCurve (0 : C(AddCircle (2 : ℝ),ℂ)) = 0 := by ext s; rfl
  rw [hQ,classicalHillFlow_free_cosine]

/-- The ORIGINAL Dirichlet energy label at zero is exactly the original
free energy, including every low positive label. -/
theorem hillDirichletEnergy_free
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (n : ℕ) (hn : 1 ≤ n) : hillDirichletEnergy 0 h0q h0r n hn = freeHillValue n := by
  have hmem := hillDirichletEnergy_mem_gap 0 h0q h0r n hn
  obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r n hn
  rw [hl,hu] at hmem
  exact le_antisymm hmem.2 hmem.1

/-- The ORIGINAL physical Dirichlet state at zero has precisely the
free sine normalization used in its actual spectral gradients. -/
theorem hillDirichletStateCurve_free
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (n : ℕ) (hn : 1 ≤ n) (t : Icc (0 : ℝ) 1) :
    hillDirichletStateCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn t =
      (sin ((n : ℂ)*Real.pi*t.val)/((n : ℂ)*Real.pi),cos ((n : ℂ)*Real.pi*t.val)) := by
  have hz : (n : ℂ)*Real.pi ≠ 0 := mul_ne_zero
    (by exact_mod_cast (by omega : n ≠ 0)) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [hillDirichletStateCurve,hillDirichletEnergy_free h0q h0r n hn,map_zero,hillFreeGap_sqrt]
  exact hillL2FrequencyStateCurve_free_sine _ hz t

/-- The ORIGINAL physical cosine state at zero retains its fixed
value-one initial normalization at every positive Dirichlet label. -/
theorem hillDirichletCosineCurve_free
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (n : ℕ) (hn : 1 ≤ n) (t : Icc (0 : ℝ) 1) :
    hillDirichletCosineCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn t =
      (cos ((n : ℂ)*Real.pi*t.val),-((n : ℂ)*Real.pi)*sin ((n : ℂ)*Real.pi*t.val)) := by
  rw [hillDirichletCosineCurve,hillDirichletEnergy_free h0q h0r n hn,map_zero,hillFreeGap_sqrt]
  exact hillL2FrequencyStateCurve_free_cosine _ t

end NLS.KdV
