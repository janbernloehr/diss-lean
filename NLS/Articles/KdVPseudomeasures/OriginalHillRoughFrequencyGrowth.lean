import NLS.Articles.KdVPseudomeasures.OriginalHillRoughFrequencySequence
import NLS.SequenceSpaces.OddPositiveFrequency

/-! The genuine rough frequency has at most cubic growth. The exact
renormalized weighted endpoint sequence bounds the correction linearly. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff NLS.LpSequence
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

def hillRoughKdVFrequencyGrowthConstant (q : HillRealMeanZeroSource) : ℝ :=
  (2*Real.pi)^3+‖hillRoughKdVRenormalizedFrequencySequence ⊤ q‖

theorem hillRoughKdVFrequencyGrowthConstant_pos (q : HillRealMeanZeroSource) :
    0 < hillRoughKdVFrequencyGrowthConstant q := by
  dsimp only [hillRoughKdVFrequencyGrowthConstant]
  positivity

theorem hillRoughKdVFrequency_remainder_bound (q : HillRealMeanZeroSource) (n : ℕ+) :
    ‖(hillRoughKdVFrequency n q:ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3‖ ≤
      ‖hillRoughKdVRenormalizedFrequencySequence ⊤ q‖*(n:ℝ) := by
  have h := WeightedCoeff.norm_apply_le (Weight.signedSobolev (-1)) ⊤ (hillRoughKdVRenormalizedFrequencySequence ⊤ q) (n:ℤ)
  rw [hillRoughKdVRenormalizedFrequencySequence_coefficients (by simp),positiveScalarExtension_apply] at h
  have hn : (1:ℝ)≤(n:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr n.pos)
  have hw : Weight.signedSobolev (-1) (n:ℤ)=(n:ℝ)⁻¹ := by
    change (max 1 |(n:ℝ)|)^(-1:ℝ)=_
    rw [abs_of_nonneg (by positivity),max_eq_right hn,Real.rpow_neg_one]
  simpa only [hw,div_inv_eq_mul] using h

theorem hillRoughKdVFrequency_cubic_bound (q : HillRealMeanZeroSource) (n : ℕ+) :
    ‖hillRoughKdVFrequency n q‖ ≤ hillRoughKdVFrequencyGrowthConstant q*(n:ℝ)^3 := by
  have h := hillRoughKdVFrequency_remainder_bound q n
  have he : ((hillRoughKdVFrequency n q-(2*Real.pi*(n:ℕ))^3:ℝ):ℂ)=
      (hillRoughKdVFrequency n q:ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3 := by push_cast; rfl
  rw [← he,Complex.norm_real] at h
  have hn : (1:ℝ)≤(n:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr n.pos)
  have hn3 : (n:ℝ)≤(n:ℝ)^3 := by
    calc
      (n:ℝ) = (n:ℝ)*1 := (mul_one _).symm
      _ ≤ (n:ℝ)*(n:ℝ)^2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hn) (by positivity)
      _ = _ := by ring
  have hc : 0 ≤ (2*Real.pi*(n:ℕ):ℝ)^3 := by positivity
  calc
    ‖hillRoughKdVFrequency n q‖ ≤ ‖hillRoughKdVFrequency n q-(2*Real.pi*(n:ℕ))^3‖+
        ‖(2*Real.pi*(n:ℕ):ℝ)^3‖ := norm_le_norm_sub_add _ _
    _ ≤ ‖hillRoughKdVRenormalizedFrequencySequence ⊤ q‖*(n:ℝ)+
        (2*Real.pi*(n:ℕ):ℝ)^3 := by rw [Real.norm_of_nonneg hc]; exact add_le_add h le_rfl
    _ ≤ ‖hillRoughKdVRenormalizedFrequencySequence ⊤ q‖*(n:ℝ)^3+
        (2*Real.pi*(n:ℕ):ℝ)^3 := add_le_add (mul_le_mul_of_nonneg_left hn3 (norm_nonneg _)) le_rfl
    _ = _ := by dsimp only [hillRoughKdVFrequencyGrowthConstant]; ring

theorem hillRoughKdVSignedFrequency_cubic_bound (q : HillRealMeanZeroSource) (k : ℤ) :
    ‖oddPositiveFrequency (fun n => hillRoughKdVFrequency n q) k‖ ≤
      hillRoughKdVFrequencyGrowthConstant q*(max 1 |(k:ℝ)|)^3 := by
  by_cases hk : k=0
  · subst k
    rw [oddPositiveFrequency_zero,norm_zero]
    exact mul_nonneg (hillRoughKdVFrequencyGrowthConstant_pos q).le (by positivity)
  let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr hk⟩
  have hn : (n:ℝ)=|(k:ℝ)| := by
    change (k.natAbs:ℝ)=|(k:ℝ)|
    simpa only [Int.cast_natCast,Int.cast_abs] using
      congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs k)
  have hkabs : (1:ℝ)≤|(k:ℝ)| := by rw [← hn]; exact_mod_cast (Nat.succ_le_iff.mpr n.pos)
  have hs : ‖(k.sign:ℝ)‖=1 := by
    rcases lt_or_gt_of_ne hk with hneg | hpos
    · rw [Int.sign_eq_neg_one_of_neg hneg]; norm_num
    · rw [Int.sign_eq_one_of_pos hpos]; norm_num
  change ‖(k.sign:ℝ)*(if h : k=0 then 0 else hillRoughKdVFrequency ⟨k.natAbs,Int.natAbs_pos.mpr h⟩ q)‖≤_
  rw [dif_neg hk,norm_mul,hs,one_mul]
  simpa only [hn,max_eq_right hkabs] using hillRoughKdVFrequency_cubic_bound q n

end NLS.Articles.KdVPseudomeasures
