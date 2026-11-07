import NLS.SequenceSpaces.WeightComparison
import NLS.SequenceSpaces.SignedSobolevWeight
import NLS.SequenceSpaces.FourierRealZeroSubmodule
import NLS.FunctionalAnalysis.ComplexEquivRealRestriction

/-! Literal identity of coefficients between the native signed bracket
max(1,abs(k)) and the article bracket 1+abs(k). The norms are NOT identified:
for nonnegative order s, the forward bound is2^s and the reverse bound is1. -/
noncomputable section
open scoped ENNReal
namespace NLS.Weight

theorem signedSobolev_le_sobolev (s : ℝ) (hs : 0 ≤ s) (k : ℤ) :
    signedSobolev s k ≤ sobolev s k := by
  apply Real.rpow_le_rpow (by positivity)
  · exact max_le (by linarith [abs_nonneg (k:ℝ)]) (by linarith)
  · exact hs

theorem sobolev_le_two_rpow_mul_signedSobolev (s : ℝ) (hs : 0 ≤ s) (k : ℤ) :
    sobolev s k ≤ (2:ℝ)^s*signedSobolev s k := by
  have hb : 0 ≤ max 1 |(k:ℝ)| := (by positivity)
  have hh : 1+|(k:ℝ)| ≤ 2*max 1 |(k:ℝ)| := by
    nlinarith [le_max_left (1:ℝ) |(k:ℝ)|,le_max_right (1:ℝ) |(k:ℝ)|]
  have h := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 1+|(k:ℝ)|) hh hs
  change (1+|(k:ℝ)|)^s ≤ (2:ℝ)^s*(max 1 |(k:ℝ)|)^s
  simpa only [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hb] using h

end NLS.Weight
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def signedSobolevPositiveEquiv (s : ℝ) (hs : 0 ≤ s) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WeightedCoeff (Weight.signedSobolev s) p ≃L[ℂ] WeightedCoeff (Weight.sobolev s) p :=
  WeightComparison.equiv _ _ ((2:ℝ)^s) 1 (Real.rpow_nonneg (by norm_num) s) zero_le_one
    (Weight.sobolev_le_two_rpow_mul_signedSobolev s hs)
    (by simpa only [one_mul] using Weight.signedSobolev_le_sobolev s hs)

theorem signedSobolevPositiveEquiv_apply (s : ℝ) (hs : 0 ≤ s)
    (a : WeightedCoeff (Weight.signedSobolev s) p) (k : ℤ) :
    (signedSobolevPositiveEquiv s hs p a).val k=a.val k :=
  WeightComparison.equiv_apply _ _ _ _ _ _ _ _ a k

theorem signedSobolevPositiveEquiv_symm_apply (s : ℝ) (hs : 0 ≤ s)
    (a : WeightedCoeff (Weight.sobolev s) p) (k : ℤ) :
    ((signedSobolevPositiveEquiv s hs p).symm a).val k=a.val k :=
  WeightComparison.equiv_symm_apply _ _ _ _ _ _ _ _ a k

theorem signedSobolevPositiveEquiv_map_zeroMode (s : ℝ) (hs : 0 ≤ s) :
    (zeroModeSubmodule (Weight.signedSobolev s) p).map (signedSobolevPositiveEquiv s hs p).toLinearMap=
      zeroModeSubmodule (Weight.sobolev s) p := by
  apply le_antisymm
  · rintro b ⟨a,ha,rfl⟩
    exact (signedSobolevPositiveEquiv_apply s hs a 0).trans ha
  · intro b hb
    refine ⟨(signedSobolevPositiveEquiv s hs p).symm b,?_,
      (signedSobolevPositiveEquiv s hs p).apply_symm_apply b⟩
    exact (signedSobolevPositiveEquiv_symm_apply s hs b 0).trans hb

def zeroModeSignedSobolevPositiveEquiv (s : ℝ) (hs : 0 ≤ s) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    zeroModeSubmodule (Weight.signedSobolev s) p ≃L[ℂ] zeroModeSubmodule (Weight.sobolev s) p :=
  (signedSobolevPositiveEquiv s hs p).ofSubmodules _ _ (signedSobolevPositiveEquiv_map_zeroMode s hs)

theorem zeroModeSignedSobolevPositiveEquiv_map_real (s : ℝ) (hs : 0 ≤ s) :
    (fourierRealZeroSubmodule (Weight.signedSobolev s) p).map
      (NLS.FunctionalAnalysis.complexEquivRealRestriction (zeroModeSignedSobolevPositiveEquiv s hs p)).toLinearMap=
        fourierRealZeroSubmodule (Weight.sobolev s) p := by
  apply le_antisymm
  · rintro b ⟨a,ha,rfl⟩ k
    change (signedSobolevPositiveEquiv s hs p a.val).val (-k)=
      (starRingEnd ℂ) ((signedSobolevPositiveEquiv s hs p a.val).val k)
    simpa only [signedSobolevPositiveEquiv_apply] using ha k
  · intro b hb
    refine ⟨(zeroModeSignedSobolevPositiveEquiv s hs p).symm b,?_,
      (zeroModeSignedSobolevPositiveEquiv s hs p).apply_symm_apply b⟩
    intro k
    change ((signedSobolevPositiveEquiv s hs p).symm b.val).val (-k)=
      (starRingEnd ℂ) (((signedSobolevPositiveEquiv s hs p).symm b.val).val k)
    simpa only [signedSobolevPositiveEquiv_symm_apply] using hb k

/-- The actual coefficient identity between the physical real zero-mode Banach spaces. -/
def physicalSignedSobolevPositiveEquiv (s : ℝ) (hs : 0 ≤ s) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    fourierRealZeroSubmodule (Weight.signedSobolev s) p ≃L[ℝ]
      fourierRealZeroSubmodule (Weight.sobolev s) p :=
  (NLS.FunctionalAnalysis.complexEquivRealRestriction (zeroModeSignedSobolevPositiveEquiv s hs p)).ofSubmodules _ _
    (zeroModeSignedSobolevPositiveEquiv_map_real s hs)

theorem physicalSignedSobolevPositiveEquiv_apply (s : ℝ) (hs : 0 ≤ s)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev s) p) (k : ℤ) :
    (physicalSignedSobolevPositiveEquiv s hs p a).val.val.val k=a.val.val.val k :=
  signedSobolevPositiveEquiv_apply s hs a.val.val k

theorem physicalSignedSobolevPositiveEquiv_symm_apply (s : ℝ) (hs : 0 ≤ s)
    (a : fourierRealZeroSubmodule (Weight.sobolev s) p) (k : ℤ) :
    ((physicalSignedSobolevPositiveEquiv s hs p).symm a).val.val.val k=a.val.val.val k :=
  signedSobolevPositiveEquiv_symm_apply s hs a.val.val k

theorem norm_physicalSignedSobolevPositiveEquiv_le (s : ℝ) (hs : 0 ≤ s)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev s) p) :
    ‖physicalSignedSobolevPositiveEquiv s hs p a‖ ≤ (2:ℝ)^s*‖a‖ :=
  WeightComparison.norm_map_le (p := p) (Weight.signedSobolev s) (Weight.sobolev s) ((2:ℝ)^s)
    (Real.rpow_nonneg (by norm_num) s) (Weight.sobolev_le_two_rpow_mul_signedSobolev s hs) a.val.val

theorem norm_physicalSignedSobolevPositiveEquiv_symm_le (s : ℝ) (hs : 0 ≤ s)
    (a : fourierRealZeroSubmodule (Weight.sobolev s) p) :
    ‖(physicalSignedSobolevPositiveEquiv s hs p).symm a‖ ≤ ‖a‖ := by
  have h := WeightComparison.norm_map_le (p := p) (Weight.sobolev s) (Weight.signedSobolev s) 1
    zero_le_one (by simpa only [one_mul] using Weight.signedSobolev_le_sobolev s hs) a.val.val
  change ‖WeightComparison.map (Weight.sobolev s) (Weight.signedSobolev s) 1 zero_le_one
    (by simpa only [one_mul] using Weight.signedSobolev_le_sobolev s hs) a.val.val‖ ≤ ‖a.val.val‖
  simpa only [one_mul] using h

end NLS.WeightedCoeff
