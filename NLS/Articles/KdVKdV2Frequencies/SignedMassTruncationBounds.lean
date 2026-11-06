import NLS.Articles.KdVKdV2Frequencies.SignedMassDivergence

/-! # Uniform endpoint mass bounds for symmetric signed truncations -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.Articles.KdVKdV2Frequencies

theorem kdvFiniteMass_signedTruncate_le (w : Weight) (N : ℕ)
    (a : SignedCoordinates w 2) (ha : HasHalfRegularity a) :
    kdvFiniteMass (signedTruncate w N a)≤kdvFiniteMass a := by
  apply Summable.tsum_le_tsum _
    ((hasHalfRegularity_iff_summable_kdvMassTerm _).mp (hasHalfRegularity_signedTruncate w N a))
    ((hasHalfRegularity_iff_summable_kdvMassTerm _).mp ha)
  intro n
  unfold kdvMassTerm
  change (2*(n : ℝ)*Real.pi)*
      ‖(WeightedCoeff.truncate w 2 (Finset.Icc (-(N : ℤ)) N) a.val).val (n : ℤ)‖^2≤_
  rw [WeightedCoeff.truncate_apply]
  split_ifs
  · exact le_rfl
  · simp only [norm_zero,zero_pow (by decide : (2 : ℕ)≠0),mul_zero]
    positivity

theorem two_kdvFiniteMass_eq_shifted_norm_sum {w : Weight}
    (a : SignedCoordinates w 2) (ha : HasHalfRegularity a) :
    2*kdvFiniteMass a=∑' k : ℕ, (4*Real.pi*(k+1 : ℕ))*‖a.val.val ((k+1 : ℕ) : ℤ)‖^2 := by
  have hs := (hasHalfRegularity_iff_summable_kdvMassTerm a).mp ha
  unfold kdvFiniteMass
  rw [hs.tsum_eq_zero_add]
  simp only [kdvMassTerm,Nat.cast_zero,mul_zero,zero_mul,zero_add]
  rw [←tsum_mul_left]
  apply tsum_congr
  intro k
  ring

end NLS.Articles.KdVKdV2Frequencies
