import NLS.ZakharovShabat.SourceSobolevFourthClassicalVariation
import NLS.MKdV.ClassicalFourthFlowRestriction
import NLS.Poisson.SourceHamiltonianDirection
import NLS.Fourier.DistributionModulation

/-! # Original Fourier coefficients of the physical H₄ cotangent

Testing the actual native physical derivative on every signed Fourier mode
identifies both Hilbert cotangent components with the reflected classical
gradient. The original source Poisson operator then yields precisely the
certified third-order physical fourth vector field.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.Fourier NLS.Poisson NLS.MKdV
open scoped ContDiff
namespace NLS.ZakharovShabat

private def fourthCotangentMode (n : ℤ) : ℝ → ℂ :=
  fun x => periodOneSobolevSynthesis (scalarMode (p := 2) n 1) (x : AddCircle (2:ℝ))

private theorem smooth_fourthCotangentMode (n : ℤ) : ContDiff ℝ ∞ (fourthCotangentMode n) := by
  change ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis (scalarMode (p := 2) n 1) (x : AddCircle (2:ℝ)))
  simpa only [periodOneSobolevSynthesis_scalarMode,one_mul] using contDiff_wave_infty (2*n)

private theorem fourthCotangentMode_coefficients (n k : ℤ) :
    (WeightedCoeff.single (p := 2) (sourceFrequencyWeight fourthSobolevSpectralWeight) n 1).val k =
      periodOneCoefficient (fourthCotangentMode n) k := by
  change _ = periodOneCoefficient (fun x : ℝ => periodOneSobolevSynthesis (scalarMode (p := 2) n 1) (x : AddCircle (2:ℝ))) k
  rw [periodOneCoefficient_periodOneSobolevSynthesis]
  simp only [WeightedCoeff.single_val,scalarMode_apply,Pi.single_apply]

private theorem fourthCotangentMode_pairing (n : ℤ) (g : ℝ → ℂ) :
    (∫ x in (0:ℝ)..1, fourthCotangentMode n x*g x) = periodOneCoefficient g (-n) := by
  simp only [fourthCotangentMode,periodOneSobolevSynthesis_scalarMode,one_mul]
  change _ = fourierCoeffOn (by norm_num : (0:ℝ) < 1) _ (-n)
  rw [← unitFourierCoefficient_eq_fourierCoeffOn,unitFourierCoefficient]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [mul_neg,neg_neg]
  ring

/-- First Hilbert cotangent coefficients are exactly the reflected physical
H₄ gradient, for any cotangent calibrated on the full native complex source. -/
theorem cotangentCoefficients_physicalFourth_fst
    (a : WeightedCoeffPair (sourceFrequencyWeight fourthSobolevSpectralWeight) 2)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (ha : ∀ k, a.fst.val k = periodOneCoefficient f k)
    (hb : ∀ k, a.snd.val k = periodOneCoefficient g k)
    (L : CoeffPair 2 →L[ℂ] ℂ)
    (hL : HasFDerivAt sourceComplexSobolevFourthHamiltonian
      (L.comp (originalWeightedSourceCLM fourthSobolevSpectralWeight)) a) (n : ℤ) :
    (CoeffPair.cotangentCoefficients le_rfl L).1 n =
      periodOneCoefficient (classicalNLSFourthGradient f g).1 (-n) := by
  let q := WeightedCoeff.single (p := 2) (sourceFrequencyWeight fourthSobolevSpectralWeight) n 1
  let v := WeightedCoeffPair.inlCLM (sourceFrequencyWeight fourthSobolevSpectralWeight) q
  have hv := hasDerivAt_sourceComplexSobolevFourthHamiltonian_fst a q f g (fourthCotangentMode n)
    hf hg (smooth_fourthCotangentMode n) hpf hpg (periodOneSobolevSynthesis_periodic _) ha hb
    (fourthCotangentMode_coefficients n)
  have hline : HasDerivAt (fun z : ℂ => a+z • v) v 0 := by
    simpa only [one_smul] using! ((hasDerivAt_id (0:ℂ)).smul_const v).const_add a
  have hL' : HasFDerivAt sourceComplexSobolevFourthHamiltonian
      (L.comp (originalWeightedSourceCLM fourthSobolevSpectralWeight)) (a+(0:ℂ) • v) := by
    simpa only [zero_smul,add_zero] using hL
  have hc := hL'.comp_hasDerivAt 0 hline
  change HasDerivAt (fun z : ℂ => sourceComplexSobolevFourthHamiltonian (a+z • v)) _ 0 at hc
  have hd := hc.unique hv
  change L (originalWeightedSourceCLM fourthSobolevSpectralWeight v) = _ at hd
  dsimp only [v,q] at hd
  rw [originalWeightedSourceCLM_inl_single] at hd
  rw [CoeffPair.cotangentCoefficients_fst,hd,fourthCotangentMode_pairing]

/-- Second Hilbert cotangent coefficients retain the other actual physical
H₄ gradient, with the same original signed-frequency reflection. -/
theorem cotangentCoefficients_physicalFourth_snd
    (a : WeightedCoeffPair (sourceFrequencyWeight fourthSobolevSpectralWeight) 2)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (ha : ∀ k, a.fst.val k = periodOneCoefficient f k)
    (hb : ∀ k, a.snd.val k = periodOneCoefficient g k)
    (L : CoeffPair 2 →L[ℂ] ℂ)
    (hL : HasFDerivAt sourceComplexSobolevFourthHamiltonian
      (L.comp (originalWeightedSourceCLM fourthSobolevSpectralWeight)) a) (n : ℤ) :
    (CoeffPair.cotangentCoefficients le_rfl L).2 n =
      periodOneCoefficient (classicalNLSFourthGradient f g).2 (-n) := by
  let q := WeightedCoeff.single (p := 2) (sourceFrequencyWeight fourthSobolevSpectralWeight) n 1
  let v := WeightedCoeffPair.inrCLM (sourceFrequencyWeight fourthSobolevSpectralWeight) q
  have hv := hasDerivAt_sourceComplexSobolevFourthHamiltonian_snd a q f g (fourthCotangentMode n)
    hf hg (smooth_fourthCotangentMode n) hpf hpg (periodOneSobolevSynthesis_periodic _) ha hb
    (fourthCotangentMode_coefficients n)
  have hline : HasDerivAt (fun z : ℂ => a+z • v) v 0 := by
    simpa only [one_smul] using! ((hasDerivAt_id (0:ℂ)).smul_const v).const_add a
  have hL' : HasFDerivAt sourceComplexSobolevFourthHamiltonian
      (L.comp (originalWeightedSourceCLM fourthSobolevSpectralWeight)) (a+(0:ℂ) • v) := by
    simpa only [zero_smul,add_zero] using hL
  have hc := hL'.comp_hasDerivAt 0 hline
  change HasDerivAt (fun z : ℂ => sourceComplexSobolevFourthHamiltonian (a+z • v)) _ 0 at hc
  have hd := hc.unique hv
  change L (originalWeightedSourceCLM fourthSobolevSpectralWeight v) = _ at hd
  dsimp only [v,q] at hd
  rw [originalWeightedSourceCLM_inr_single] at hd
  rw [CoeffPair.cotangentCoefficients_snd,hd,fourthCotangentMode_pairing]

/-- Applying the actual original Poisson operator to the calibrated H₄
cotangent gives both precise physical third-order vector-field coefficients. -/
theorem sourceHamiltonianDirection_physicalFourth_coordinates
    (a : WeightedCoeffPair (sourceFrequencyWeight fourthSobolevSpectralWeight) 2)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (ha : ∀ k, a.fst.val k = periodOneCoefficient f k)
    (hb : ∀ k, a.snd.val k = periodOneCoefficient g k)
    (L : CoeffPair 2 →L[ℂ] ℂ)
    (hL : HasFDerivAt sourceComplexSobolevFourthHamiltonian
      (L.comp (originalWeightedSourceCLM fourthSobolevSpectralWeight)) a) (n : ℤ) :
    (sourceHamiltonianDirection le_rfl L).fst n = periodOneCoefficient (classicalNLSFourthVectorField f g).1 n ∧
      (sourceHamiltonianDirection le_rfl L).snd n = periodOneCoefficient (classicalNLSFourthVectorField f g).2 n := by
  constructor
  · change -I*(CoeffPair.cotangentCoefficients le_rfl L).2 (-n) = _
    rw [cotangentCoefficients_physicalFourth_snd a f g hf hg hpf hpg ha hb L hL,neg_neg]
    simp only [periodOneCoefficient,← unitFourierCoefficient_eq_fourierCoeffOn,
      unitFourierCoefficient,classicalNLSFourthVectorField,mul_assoc,intervalIntegral.integral_const_mul]
  · change I*(CoeffPair.cotangentCoefficients le_rfl L).1 (-n) = _
    rw [cotangentCoefficients_physicalFourth_fst a f g hf hg hpf hpg ha hb L hL,neg_neg]
    simp only [periodOneCoefficient,← unitFourierCoefficient_eq_fourierCoeffOn,
      unitFourierCoefficient,classicalNLSFourthVectorField,mul_assoc,intervalIntegral.integral_const_mul]

end NLS.ZakharovShabat
