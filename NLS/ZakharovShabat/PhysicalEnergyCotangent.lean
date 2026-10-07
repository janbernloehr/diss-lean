import NLS.ZakharovShabat.PeriodOneSobolevEnergyVariation
import NLS.ZakharovShabat.SourceSobolevEmbedding
import NLS.ZakharovShabat.ClassicalNLSVectorField
import NLS.Poisson.SourceHamiltonianDirection
import NLS.Fourier.DistributionModulation

/-! # Physical Fourier coefficients of the energy cotangent

Testing an H¹ energy derivative against every signed Fourier mode identifies
both original Hilbert cotangent components with the reflected coefficients
of the classical spatial gradient. The source Poisson direction consequently
has precisely the Fourier coefficients of the classical NLS vector field.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.Poisson
open scoped ContDiff
namespace NLS.ZakharovShabat

@[simp] theorem sobolevSourceInclusion_scalarMode_fst (n : ℤ) :
    sobolevSourceInclusion (scalarMode n 1,0) = CoeffPair.inlCLM (lp.single 2 n 1) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext k <;>
    simp [sobolevSourceInclusion_fst,sobolevSourceInclusion_snd,scalarMode_apply,
      CoeffPair.inlCLM_fst,CoeffPair.inlCLM_snd,lp.single_apply,Pi.single_apply]

@[simp] theorem sobolevSourceInclusion_scalarMode_snd (n : ℤ) :
    sobolevSourceInclusion (0,scalarMode n 1) = CoeffPair.inrCLM (lp.single 2 n 1) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext k <;>
    simp [sobolevSourceInclusion_fst,sobolevSourceInclusion_snd,scalarMode_apply,
      CoeffPair.inrCLM_fst,CoeffPair.inrCLM_snd,lp.single_apply,Pi.single_apply]

/-- The fst cotangent component is the reflected physical energy gradient. -/
theorem cotangentCoefficients_physicalEnergy_fst (a b : ScalarDomain 2)
    (ha : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ))))
    (L : CoeffPair 2 →L[ℂ] ℂ)
    (hL : HasFDerivAt periodOneSobolevHamiltonian (L.comp sobolevSourceInclusion) (a,b)) (n : ℤ) :
    (CoeffPair.cotangentCoefficients le_rfl L).1 n = periodOneCoefficient
      (classicalNLSEnergyGradient
        (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)))
        (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ)))).1 (-n) := by
  have hm : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis (scalarMode (p := 2) n 1)
      (x : AddCircle (2 : ℝ))) := by
    simpa only [periodOneSobolevSynthesis_scalarMode,one_mul] using contDiff_wave_infty (2*n)
  have hv := hasDerivAt_periodOneSobolevHamiltonian_fst a b (scalarMode n 1) ha hb hm
  have hline : HasDerivAt (fun z : ℂ => (a+z • scalarMode n 1,b)) (scalarMode n 1,0) 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).smul_const (scalarMode (p := 2) n 1)).const_add a).prodMk (hasDerivAt_const 0 b)
  have hL' : HasFDerivAt periodOneSobolevHamiltonian (L.comp sobolevSourceInclusion)
      (a+(0 : ℂ) • scalarMode n 1,b) := by simpa only [zero_smul,add_zero] using hL
  have hc := hL'.comp_hasDerivAt 0 hline
  simp only [Function.comp_def] at hc
  have hd := hc.unique hv
  rw [CoeffPair.cotangentCoefficients_fst]
  change L (sobolevSourceInclusion (scalarMode n 1,0)) = _ at hd
  simp only [sobolevSourceInclusion_scalarMode_fst,periodOneSobolevSynthesis_scalarMode,one_mul] at hd
  rw [hd]
  change _ = fourierCoeffOn (by norm_num : (0 : ℝ) < 1) _ (-n)
  rw [← unitFourierCoefficient_eq_fourierCoeffOn,unitFourierCoefficient]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [mul_neg,neg_neg]
  ring

/-- The snd cotangent component is the reflected physical energy gradient. -/
theorem cotangentCoefficients_physicalEnergy_snd (a b : ScalarDomain 2)
    (ha : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ))))
    (L : CoeffPair 2 →L[ℂ] ℂ)
    (hL : HasFDerivAt periodOneSobolevHamiltonian (L.comp sobolevSourceInclusion) (a,b)) (n : ℤ) :
    (CoeffPair.cotangentCoefficients le_rfl L).2 n = periodOneCoefficient
      (classicalNLSEnergyGradient
        (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)))
        (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ)))).2 (-n) := by
  have hm : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis (scalarMode (p := 2) n 1)
      (x : AddCircle (2 : ℝ))) := by
    simpa only [periodOneSobolevSynthesis_scalarMode,one_mul] using contDiff_wave_infty (2*n)
  have hv := hasDerivAt_periodOneSobolevHamiltonian_snd a b (scalarMode n 1) ha hb hm
  have hline : HasDerivAt (fun z : ℂ => (a,b+z • scalarMode n 1)) (0,scalarMode n 1) 0 := by
    simpa using (hasDerivAt_const (0 : ℂ) a).prodMk
      (((hasDerivAt_id (0 : ℂ)).smul_const (scalarMode (p := 2) n 1)).const_add b)
  have hL' : HasFDerivAt periodOneSobolevHamiltonian (L.comp sobolevSourceInclusion)
      (a,b+(0 : ℂ) • scalarMode n 1) := by simpa only [zero_smul,add_zero] using hL
  have hc := hL'.comp_hasDerivAt 0 hline
  simp only [Function.comp_def] at hc
  have hd := hc.unique hv
  rw [CoeffPair.cotangentCoefficients_snd]
  change L (sobolevSourceInclusion (0,scalarMode n 1)) = _ at hd
  simp only [sobolevSourceInclusion_scalarMode_snd,periodOneSobolevSynthesis_scalarMode,one_mul] at hd
  rw [hd]
  change _ = fourierCoeffOn (by norm_num : (0 : ℝ) < 1) _ (-n)
  rw [← unitFourierCoefficient_eq_fourierCoeffOn,unitFourierCoefficient]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [mul_neg,neg_neg]
  ring

/-- The original source Hamiltonian direction has the physical NLS Fourier coefficients. -/
theorem sourceHamiltonianDirection_physicalEnergy_coordinates (a b : ScalarDomain 2)
    (ha : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ))))
    (L : CoeffPair 2 →L[ℂ] ℂ)
    (hL : HasFDerivAt periodOneSobolevHamiltonian (L.comp sobolevSourceInclusion) (a,b)) (n : ℤ) :
    (sourceHamiltonianDirection le_rfl L).fst n = periodOneCoefficient
      (classicalNLSVectorField
        (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)))
        (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ)))).1 n ∧
    (sourceHamiltonianDirection le_rfl L).snd n = periodOneCoefficient
      (classicalNLSVectorField
        (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)))
        (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ)))).2 n := by
  constructor
  · change -I*(CoeffPair.cotangentCoefficients le_rfl L).2 (-n) = _
    rw [cotangentCoefficients_physicalEnergy_snd a b ha hb L hL,neg_neg]
    simp only [periodOneCoefficient,← unitFourierCoefficient_eq_fourierCoeffOn,
      unitFourierCoefficient,classicalNLSVectorField,mul_assoc,intervalIntegral.integral_const_mul]
  · change I*(CoeffPair.cotangentCoefficients le_rfl L).1 (-n) = _
    rw [cotangentCoefficients_physicalEnergy_fst a b ha hb L hL,neg_neg]
    simp only [periodOneCoefficient,← unitFourierCoefficient_eq_fourierCoeffOn,
      unitFourierCoefficient,classicalNLSVectorField,mul_assoc,intervalIntegral.integral_const_mul]

end NLS.ZakharovShabat
