import NLS.ZakharovShabat.SobolevOddHamiltonian
import NLS.ZakharovShabat.SobolevRiccatiClassicalAgreement
import NLS.ZakharovShabat.SobolevSourceSmoothDensity

/-! # Sharp odd Hamiltonians including the mass endpoint

The existing reduced-polynomial construction covers H_(2s+1) on H^s for
s>=1. The original H_1 mass supplies the s=0 endpoint with the same physical
normalization. This adapter asserts no new spectral identity.
-/
noncomputable section
open NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

def sharpOddNLSHamiltonian (s : ℕ) (ab : SobolevSource s) : ℂ :=
  if hs : 1 ≤ s then sobolevOddHamiltonian s hs ab
  else sobolevNLSHamiltonian s ab 1 (by omega)

theorem analyticAt_sharpOddNLSHamiltonian (s : ℕ) (ab : SobolevSource s) :
    AnalyticAt ℂ (sharpOddNLSHamiltonian s) ab := by
  unfold sharpOddNLSHamiltonian
  split_ifs
  · exact analyticAt_sobolevOddHamiltonian s _ ab
  · exact analyticAt_sobolevNLSHamiltonian s 1 (by omega) ab

theorem sharpOddNLSHamiltonian_eq_classical (s : ℕ) (ab : SobolevSource s)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (hfc : ∀ j, ab.1.val j = periodOneCoefficient f j)
    (hgc : ∀ j, ab.2.val j = periodOneCoefficient g j) :
    sharpOddNLSHamiltonian s ab = classicalNLSHamiltonian f g (2*s+1) := by
  unfold sharpOddNLSHamiltonian
  split_ifs with hs
  · exact sobolevOddHamiltonian_eq_classical s hs ab f g hf hg hpf hpg hfc hgc
  · rw [show 2*s+1 = 1 by omega]
    exact sobolevNLSHamiltonian_eq_classical s ab f g hf hg hpf hpg hfc hgc 1 (by omega)

theorem sharpOddNLSHamiltonian_unique_continuous (s : ℕ) (F : SobolevSource s → ℂ)
    (hF : Continuous F)
    (hclassical : ∀ (ab : SobolevSource s) (f g : ℝ → ℂ), ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      Function.Periodic f 1 → Function.Periodic g 1 →
      (∀ j, ab.1.val j = periodOneCoefficient f j) →
      (∀ j, ab.2.val j = periodOneCoefficient g j) → F ab = classicalNLSHamiltonian f g (2*s+1)) :
    F = sharpOddNLSHamiltonian s := by
  apply eq_of_continuous_of_smooth_sobolevSource s F _ hF
    (continuous_iff_continuousAt.mpr fun ab => (analyticAt_sharpOddNLSHamiltonian s ab).continuousAt)
  intro ab f g hf hg hpf hpg hfc hgc
  exact (hclassical ab f g hf hg hpf hpg hfc hgc).trans
    (sharpOddNLSHamiltonian_eq_classical s ab f g hf hg hpf hpg hfc hgc).symm

end NLS.ZakharovShabat
