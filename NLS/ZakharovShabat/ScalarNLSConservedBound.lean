import NLS.ZakharovShabat.ClassicalNLSSobolevEnergy
import NLS.ZakharovShabat.SourceSobolevEnergyCoercivity

/-! # A Fourier ℓ¹ bound from physical mass and energy -/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- Every scalar H¹ datum gives an actual real-type Sobolev source. -/
def scalarSobolevRealSource (a : ScalarDomain 2) : realTypeSobolevSourceLocus :=
  ⟨sobolevRealPairCLM a,by
    intro n
    change (sobolevSourceInclusion (a,sobolevConjugateCLM a)).snd n =
      conj ((sobolevSourceInclusion (a,sobolevConjugateCLM a)).fst (-n))
    simp only [sobolevSourceInclusion_fst,sobolevSourceInclusion_snd,sobolevConjugateCLM_apply]⟩

/-- The bilinear real-pair mass is the physical scalar mass. -/
theorem periodOneSobolevMass_realPair (a : ScalarDomain 2) :
    periodOneSobolevMass (sobolevRealPairCLM a) =
      (classicalNLSMass (periodOneSobolevSynthesis a) : ℂ) := by
  change periodOneSobolevMass (a,sobolevConjugateCLM a) = _
  rw [periodOneSobolevMass_eq_integral,
    classicalNLSMass_eq_integral _ (periodOneSobolevSynthesis_periodic a),← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [periodOneSobolevSynthesis_conjugate,Complex.mul_conj']
  norm_cast

/-- The physical conserved quantities control the full scalar H¹ norm. -/
theorem norm_scalarSobolev_sq_le_conserved (a : ScalarDomain 2) :
    ‖a‖^2 ≤ 2*(classicalNLSMass (periodOneSobolevSynthesis a)+(scalarSobolevEnergy a).re) := by
  have h := norm_sobolev_fst_sq_le_mass_energy (scalarSobolevRealSource a)
  change ‖a‖^2 ≤ 2*((periodOneSobolevMass (sobolevRealPairCLM a)).re+(scalarSobolevEnergy a).re) at h
  simpa only [periodOneSobolevMass_realPair,Complex.ofReal_re] using h

/-- A bound for the absolute Fourier norm depending only on the conserved data. -/
def nlsConservedBound (a : ScalarDomain 2) : ℝ :=
  WeightedCoeff.sobolevEmbeddingConstant 2 (by simp) *
    Real.sqrt (2*(classicalNLSMass (periodOneSobolevSynthesis a)+(scalarSobolevEnergy a).re))

theorem nlsConservedBound_nonneg (a : ScalarDomain 2) : 0 ≤ nlsConservedBound a :=
  mul_nonneg (WeightedCoeff.sobolevEmbeddingConstant_nonneg 2 (by simp)) (Real.sqrt_nonneg _)

/-- The actual absolute Fourier series is bounded by the conserved quantities. -/
theorem norm_sobolevToL1_le_conserved (a : ScalarDomain 2) :
    ‖WeightedCoeff.sobolevToL1CLM 2 (by simp) a‖ ≤ nlsConservedBound a := by
  apply (WeightedCoeff.norm_sobolevToL1CLM_le 2 (by simp) a).trans
  exact mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (norm_scalarSobolev_sq_le_conserved a))
    (WeightedCoeff.sobolevEmbeddingConstant_nonneg 2 (by simp))

/-- Matching physical mass and energy give the same absolute-norm bound. -/
theorem nlsConservedBound_eq_of_conservation (a b : ScalarDomain 2)
    (hm : classicalNLSMass (periodOneSobolevSynthesis a) = classicalNLSMass (periodOneSobolevSynthesis b))
    (he : scalarSobolevEnergy a = scalarSobolevEnergy b) : nlsConservedBound a = nlsConservedBound b := by
  simp only [nlsConservedBound,hm,he]

end NLS.ZakharovShabat
