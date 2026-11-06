import NLS.ZakharovShabat.SourceSobolevFourthComplexGerm
import NLS.ZakharovShabat.ClassicalNLSFourthVariation

/-! # The native complex H₄ derivative retains its certified physical variation

Arbitrary smooth periodic perturbations with the specified original Fourier
coefficients calibrate the native polynomial along their entire complex line.
No spectral action formula is used in this physical first-variation result.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

@[simp] theorem fourthNativeComplexSourceCLM_fst
    (a : WeightedCoeffPair (sourceFrequencyWeight fourthSobolevSpectralWeight) 2) (n : ℤ) :
    (fourthNativeComplexSourceCLM a).1.val n = a.fst.val n :=
  fourthNativeFieldCLM_apply a.fst n

@[simp] theorem fourthNativeComplexSourceCLM_snd
    (a : WeightedCoeffPair (sourceFrequencyWeight fourthSobolevSpectralWeight) 2) (n : ℤ) :
    (fourthNativeComplexSourceCLM a).2.val n = a.snd.val n :=
  fourthNativeFieldCLM_apply a.snd n

private theorem coefficient_smul (f : ℝ → ℂ) (c : ℂ) (n : ℤ) :
    periodOneCoefficient (c • f) n = c*periodOneCoefficient f n :=
  fourierCoeffOn.const_smul _ _ _ _

/-- The first native physical H₄ variation is exactly the certified
Riccati Hamiltonian variation for the same actual Fourier fields. -/
theorem hasDerivAt_sourceComplexSobolevFourthHamiltonian_fst
    (a : WeightedCoeffPair (sourceFrequencyWeight fourthSobolevSpectralWeight) 2)
    (q : WeightedCoeff (sourceFrequencyWeight fourthSobolevSpectralWeight) 2)
    (f g h : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1) (hph : Function.Periodic h 1)
    (ha : ∀ n, a.fst.val n = periodOneCoefficient f n)
    (hb : ∀ n, a.snd.val n = periodOneCoefficient g n)
    (hq : ∀ n, q.val n = periodOneCoefficient h n) :
    HasDerivAt (fun z : ℂ => sourceComplexSobolevFourthHamiltonian
      (a+z • WeightedCoeffPair.inlCLM (sourceFrequencyWeight fourthSobolevSpectralWeight) q))
      (∫ x in (0:ℝ)..1, h x*(classicalNLSFourthGradient f g).1 x) 0 := by
  have he (z : ℂ) : sourceComplexSobolevFourthHamiltonian
      (a+z • WeightedCoeffPair.inlCLM (sourceFrequencyWeight fourthSobolevSpectralWeight) q) =
      classicalNLSHamiltonian (f+z • h) g 4 := by
    apply periodOneSobolevFourthHamiltonian_eq_classical _ _ _
      (hf.add (contDiff_const.mul hh)) hg
      (by intro x; change f (x+1)+z*h (x+1) = f x+z*h x; rw [hpf x,hph x]) hpg
    · intro n
      rw [fourthNativeComplexSourceCLM_fst]
      change a.fst.val n+z*q.val n = periodOneCoefficient (f+z • h) n
      rw [periodOneCoefficient_add f (z • h) hf.continuous (continuous_const.mul hh.continuous),
        coefficient_smul,ha n,hq n]
    · intro n
      rw [fourthNativeComplexSourceCLM_snd]
      change a.snd.val n+z*0 = periodOneCoefficient g n
      simp only [mul_zero,add_zero,hb n]
  simp_rw [he]
  exact hasDerivAt_classicalNLSHamiltonian_four_fst f g h hf hg hh hpf hpg hph

/-- The second component retains its independently certified physical
gradient and the opposite cross-component Hamiltonian role. -/
theorem hasDerivAt_sourceComplexSobolevFourthHamiltonian_snd
    (a : WeightedCoeffPair (sourceFrequencyWeight fourthSobolevSpectralWeight) 2)
    (q : WeightedCoeff (sourceFrequencyWeight fourthSobolevSpectralWeight) 2)
    (f g h : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1) (hph : Function.Periodic h 1)
    (ha : ∀ n, a.fst.val n = periodOneCoefficient f n)
    (hb : ∀ n, a.snd.val n = periodOneCoefficient g n)
    (hq : ∀ n, q.val n = periodOneCoefficient h n) :
    HasDerivAt (fun z : ℂ => sourceComplexSobolevFourthHamiltonian
      (a+z • WeightedCoeffPair.inrCLM (sourceFrequencyWeight fourthSobolevSpectralWeight) q))
      (∫ x in (0:ℝ)..1, h x*(classicalNLSFourthGradient f g).2 x) 0 := by
  have he (z : ℂ) : sourceComplexSobolevFourthHamiltonian
      (a+z • WeightedCoeffPair.inrCLM (sourceFrequencyWeight fourthSobolevSpectralWeight) q) =
      classicalNLSHamiltonian f (g+z • h) 4 := by
    apply periodOneSobolevFourthHamiltonian_eq_classical _ _ _ hf
      (hg.add (contDiff_const.mul hh)) hpf
      (by intro x; change g (x+1)+z*h (x+1) = g x+z*h x; rw [hpg x,hph x])
    · intro n
      rw [fourthNativeComplexSourceCLM_fst]
      change a.fst.val n+z*0 = periodOneCoefficient f n
      simp only [mul_zero,add_zero,ha n]
    · intro n
      rw [fourthNativeComplexSourceCLM_snd]
      change a.snd.val n+z*q.val n = periodOneCoefficient (g+z • h) n
      rw [periodOneCoefficient_add g (z • h) hg.continuous (continuous_const.mul hh.continuous),
        coefficient_smul,hb n,hq n]
  simp_rw [he]
  exact hasDerivAt_classicalNLSHamiltonian_four_snd f g h hf hg hh hpf hpg hph

end NLS.ZakharovShabat
