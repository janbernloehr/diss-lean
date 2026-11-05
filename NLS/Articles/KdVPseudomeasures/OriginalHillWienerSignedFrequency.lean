import NLS.Articles.KdVPseudomeasures.OriginalHillWienerFrequencySequence
import NLS.SequenceSpaces.PositiveOddFrequencyCorrection

/-! The exact signed odd KdV frequency has its original cubic free
part plus a bounded real analytic correction on every physical Wiener
source. Reflection subtraction preserves the zero and BOTH signs. -/
noncomputable section
open Complex NLS.KdV NLS.WeightedCoeff NLS.LpSequence
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

def originalWienerSignedKdVFrequency (N : ℕ) (q : OriginalWienerPotential N) : ℤ → ℝ :=
  oddPositiveFrequency (fun n => hillRoughKdVFrequency n
    (originalHillRealMeanZeroSource (originalWienerOriginalPotential N q)))

theorem originalWienerSignedKdVFrequency_neg (N : ℕ) (q : OriginalWienerPotential N) (k : ℤ) :
    originalWienerSignedKdVFrequency N q (-k)= -originalWienerSignedKdVFrequency N q k :=
  oddPositiveFrequency_neg _ k

def originalWienerSignedFrequencyCorrection (N : ℕ) (q : OriginalWienerPotential N) : Coeff ⊤ :=
  originalWienerKdVRenormalizedFrequencySequence N q-
    Coeff.reflection (originalWienerKdVRenormalizedFrequencySequence N q)

theorem analyticAt_originalWienerSignedFrequencyCorrection (N : ℕ) (q : OriginalWienerPotential N) :
    AnalyticAt ℝ (originalWienerSignedFrequencyCorrection N) q := by
  have hA := analyticAt_originalWienerKdVRenormalizedFrequencySequence N q
  have hR := ((Coeff.reflection (p := ⊤)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).analyticAt
    (originalWienerKdVRenormalizedFrequencySequence N q)
  exact hA.sub (hR.comp (f := originalWienerKdVRenormalizedFrequencySequence N) hA)

theorem originalWienerSignedFrequencyCorrection_apply (N : ℕ) (q : OriginalWienerPotential N) (k : ℤ) :
    originalWienerSignedFrequencyCorrection N q k =
      (originalWienerSignedKdVFrequency N q k:ℂ)-(2*(Real.pi:ℂ)*(k:ℂ))^3 := by
  change originalWienerKdVRenormalizedFrequencySequence N q k-
    Coeff.reflection (originalWienerKdVRenormalizedFrequencySequence N q) k = _
  rw [Coeff.reflection_apply,originalWienerKdVRenormalizedFrequencySequence_coefficients,
    originalWienerKdVRenormalizedFrequencySequence_coefficients]
  have he : (fun n : ℕ+ => (hillRoughKdVFrequency n
      (originalHillRealMeanZeroSource (originalWienerOriginalPotential N q)):ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3) =
      (fun n : ℕ+ => (hillRoughKdVFrequency n
        (originalHillRealMeanZeroSource (originalWienerOriginalPotential N q)):ℂ)-
          (((2*Real.pi)^3:ℝ):ℂ)*(n:ℂ)^3) := by
    funext n
    push_cast
    ring
  rw [he,positive_cubic_correction_sub_reflection]
  change (originalWienerSignedKdVFrequency N q k:ℂ)-_ = _
  push_cast
  ring

theorem originalWienerSignedFrequencyCorrection_free (N : ℕ) (q : OriginalWienerPotential N) (k : ℤ) :
    (((2*Real.pi*(k:ℝ))^3:ℝ):ℂ)+originalWienerSignedFrequencyCorrection N q k =
      (originalWienerSignedKdVFrequency N q k:ℂ) := by
  rw [originalWienerSignedFrequencyCorrection_apply]
  push_cast
  ring

end NLS.Articles.KdVPseudomeasures
