import NLS.Fourier.PeriodicExponentInclusion
import NLS.KdV.SingularHillPhysical

/-! Every original Fourier-Lebesgue vector of regularity above 3/2 has a
faithful full H1 representative, for EVERY Banach exponent including infinity. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The full original strong Fourier-Lebesgue space in the native H1 domain. -/
def hillStrongSobolevToH1 (a : ℝ) (ha : 3/2 < a) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    FourierLebesgueSpace (2:ℝ) a p →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  (endpointLowerInclusion a 1 (by norm_num)
    (by norm_num only [ENNReal.toReal_ofNat];linarith : 1 < (a-1)*(2:ℝ≥0∞).toReal)).comp
      (PeriodicFourierLebesgue.exponentInclusion a (le_top : p ≤ ⊤))

/-- The H1 representative retains the ENTIRE original distribution. -/
theorem hillStrongSobolevToH1_val (a : ℝ) (ha : 3/2 < a) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : FourierLebesgueSpace (2:ℝ) a p) : (hillStrongSobolevToH1 a ha p f).val = f.val := by
  change (endpointLowerInclusion a 1 _ _ (PeriodicFourierLebesgue.exponentInclusion a (le_top : p ≤ ⊤) f)).val = _
  rw [endpointLowerInclusion_val,PeriodicFourierLebesgue.exponentInclusion_val]

/-- No original strong-space vector is lost in its native H1 realization. -/
theorem hillStrongSobolevToH1_injective (a : ℝ) (ha : 3/2 < a) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Function.Injective (hillStrongSobolevToH1 a ha p) := by
  intro f g h
  apply Subtype.ext
  simpa only [hillStrongSobolevToH1_val] using congrArg Subtype.val h

end NLS.KdV
