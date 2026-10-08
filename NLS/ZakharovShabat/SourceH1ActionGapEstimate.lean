import NLS.ZakharovShabat.SourceH1CentralProductBound
import NLS.ZakharovShabat.SourceH1GapProductReduction

/-! # Lemma 28.1 and Proposition 28.2: the real H¹ action-gap bounds

Squaring the central-product estimate recovers 2048 even at the boundary
index. This does not use the false scalar comparison audited earlier.
The real critical-point bound also improves Proposition 28.2's 4608 to 1536.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- The actual closed-gap factor obeys the printed scalar constant at an
inclusive, norm-adapted cutoff, also at cutoff zero. -/
theorem sourceH1_real_gapFactor_le_2048_at_cutoff (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) (hcut : (N:ℝ) ≤ 8*‖φ‖^2)
    (n : ℤ) (hn : N ≤ n.natAbs) :
    ‖sourceRealGapFactor (by simp) (by norm_num) ψ.val ψ.property n‖ ≤ 2048*(1+‖φ‖^2) := by
  by_cases hzero : N = 0
  · subst N
    have hsmall : 8*‖φ‖^2 ≤ 1 := by simpa using hN
    exact (sourceH1_real_gapFactor_le_128_of_small_norm ψ φ hφ hsmall n).trans
      (by nlinarith [sq_nonneg ‖φ‖])
  have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hzero
  apply (sourceRealGapFactor_norm_le_iff (by simp) (by norm_num)
    ψ.val ψ.property n (2048*(1+‖φ‖^2)) (by positivity)).mpr
  intro z hz
  have hcore := sourceH1_real_central_product_sq_le ψ φ hφ N hNpos hN n hn z hz
  have hlim := sourceH1_real_gap_product_le_128_core ψ φ hφ N hN n hn z hz
  have hnorm : ‖∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ),
      (canonicalCriticalPoints (by simp) (by norm_num) (periodOnePotential ψ.val)
        (periodOnePotential_mem ψ.val) m-z)/sourceStandardRoot (by simp) (by norm_num) ψ.val m z‖ ≤
      16*(1+‖φ‖^2) := by
    nlinarith [sq_nonneg (‖φ‖^2),sq_nonneg ‖φ‖]
  linarith

/-- Lemma 28.1's scalar bound on real H¹ sources, at every index allowed
by the quadratic localization threshold. No separate cutoff is required. -/
theorem sourceH1_real_gapFactor_le_2048 (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    ‖sourceRealGapFactor (by simp) (by norm_num) ψ.val ψ.property n‖ ≤ 2048*(1+‖φ‖^2) := by
  let K : ℕ := ⌊8*‖φ‖^2⌋₊
  let N := min n.natAbs K
  have hfloor : (K:ℝ) ≤ 8*‖φ‖^2 := Nat.floor_le (by positivity)
  have hK : 8*‖φ‖^2 ≤ 1+(K:ℝ) := by
    have h := Nat.lt_floor_add_one (8*‖φ‖^2)
    dsimp [K]
    linarith
  have hN : 8*‖φ‖^2 ≤ 1+(N:ℝ) := by
    by_cases h : n.natAbs ≤ K
    · simpa only [N,min_eq_left h,Nat.cast_natAbs,Int.cast_abs] using hn
    · simpa only [N,min_eq_right (le_of_not_ge h)] using hK
  have hcut : (N:ℝ) ≤ 8*‖φ‖^2 :=
    (show (N:ℝ) ≤ (K:ℝ) by exact_mod_cast min_le_right n.natAbs K).trans hfloor
  exact sourceH1_real_gapFactor_le_2048_at_cutoff ψ φ hφ N hN hcut n (min_le_left _ _)

/-- The stronger real-source form of Proposition 28.2, including its
collapsed-gap case and the inclusive localization boundary. -/
theorem sourceH1_real_action_le_1536_gap_sq (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    ‖sourceComplexAction (by simp) (by norm_num) n ψ.val‖ ≤
      1536*(1+‖φ‖^2)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ.val n‖^2 := by
  have h := sourceComplexAction_le_three_gapFactor_mul_gap_sq (by simp) (by norm_num) ψ.val ψ.property n
  have hfactor := sourceH1_real_gapFactor_le_2048 ψ φ hφ n hn
  have hmul := mul_le_mul_of_nonneg_right hfactor
    (sq_nonneg ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ.val n‖)
  nlinarith

/-- Proposition 28.2 with its printed constant and index threshold, on the real source locus. -/
theorem sourceH1_real_action_le_4608_gap_sq (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ |(n:ℝ)|) :
    ‖sourceComplexAction (by simp) (by norm_num) n ψ.val‖ ≤
      4608*(1+‖φ‖^2)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ.val n‖^2 := by
  have h := sourceH1_real_action_le_1536_gap_sq ψ φ hφ n (by linarith)
  have hp := mul_nonneg (by positivity : 0 ≤ 1+‖φ‖^2)
    (sq_nonneg ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ.val n‖)
  nlinarith

end NLS.ZakharovShabat
