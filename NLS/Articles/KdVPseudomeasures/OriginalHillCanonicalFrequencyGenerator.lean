import NLS.Articles.KdVPseudomeasures.OriginalHillRoughFrequencyGrowth
import NLS.SequenceSpaces.FourierRealZeroMultiplier
import NLS.SequenceSpaces.SignedSobolevWeight

/-! The GENUINE rough KdV frequency multiplier is a bounded operator
losing exactly three signed Sobolev orders on the physical real form. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff NLS.LpSequence
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem hillRoughKdVFrequency_multiplier_bound (s : ℝ) (q : HillRealMeanZeroSource) (k : ℤ) :
    Weight.signedSobolev s k*‖I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n q) k:ℂ)‖ ≤
      hillRoughKdVFrequencyGrowthConstant q*Weight.signedSobolev (s+3) k := by
  rw [norm_mul,norm_I,one_mul,Complex.norm_real]
  have hb : 0<max (1:ℝ) |(k:ℝ)| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  calc
    _ ≤ Weight.signedSobolev s k*(hillRoughKdVFrequencyGrowthConstant q*(max 1 |(k:ℝ)|)^3) :=
      mul_le_mul_of_nonneg_left (hillRoughKdVSignedFrequency_cubic_bound q k) ((Weight.signedSobolev s).positive k).le
    _ = _ := by
      change (max 1 |(k:ℝ)|)^s*(hillRoughKdVFrequencyGrowthConstant q*(max 1 |(k:ℝ)|)^3)=
        hillRoughKdVFrequencyGrowthConstant q*(max 1 |(k:ℝ)|)^(s+3)
      rw [Real.rpow_add hb,Real.rpow_ofNat]
      ring

theorem hillRoughKdVFrequency_multiplier_real (q : HillRealMeanZeroSource) (k : ℤ) :
    I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n q) (-k):ℂ)=
      (starRingEnd ℂ) (I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n q) k:ℂ)) := by
  rw [oddPositiveFrequency_neg,Complex.ofReal_neg,map_mul,Complex.conj_I,Complex.conj_ofReal]
  ring

def hillRoughKdVFrequencyGenerator (s : ℝ) (q : HillRealMeanZeroSource)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    fourierRealZeroSubmodule (Weight.signedSobolev (s+3)) p →L[ℝ]
      fourierRealZeroSubmodule (Weight.signedSobolev s) p :=
  fourierRealZeroMultiplier _ _ (Weight.signedSobolev_neg s)
    (fun k => I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n q) k:ℂ))
    (hillRoughKdVFrequencyGrowthConstant q) (hillRoughKdVFrequencyGrowthConstant_pos q).le
    (hillRoughKdVFrequency_multiplier_bound s q) (hillRoughKdVFrequency_multiplier_real q)

theorem hillRoughKdVFrequencyGenerator_apply (s : ℝ) (q : HillRealMeanZeroSource)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (s+3)) p) (k : ℤ) :
    (hillRoughKdVFrequencyGenerator s q p a).val.val.val k=
      I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n q) k:ℂ)*a.val.val.val k :=
  fourierRealZeroMultiplier_apply _ _ _ _ _ _ _ _ a k

theorem norm_hillRoughKdVFrequencyGenerator_le (s : ℝ) (q : HillRealMeanZeroSource)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (s+3)) p) :
    ‖hillRoughKdVFrequencyGenerator s q p a‖ ≤ hillRoughKdVFrequencyGrowthConstant q*‖a‖ :=
  norm_fourierRealZeroMultiplier_le _ _ _ _ _ _ _ _ a

end NLS.Articles.KdVPseudomeasures
