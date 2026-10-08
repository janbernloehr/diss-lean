import NLS.ZakharovShabat.SourceRealNormalizedActionGapBound

/-! # A strict real margin for the complex estimate of Lemma 28.1 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Sharpen the real constant to 1024, leaving margin for complex perturbations. -/
theorem sourceM1_real_gapFactor_le_1024_at_cutoff (w : SpectralWeight) (hw : w.HasLinearFactor)
    (ψ : realTypeSourceSubmodule 2) (φ : WeightedCoeffPair w.toWeight 2)
    (hφ : weightedBaseToPair w φ = periodOnePotential ψ.val)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) (hcut : (N:ℝ) ≤ 8*‖φ‖^2)
    (n : ℤ) (hn : N ≤ n.natAbs) :
    ‖sourceRealGapFactor (by simp) (by norm_num) ψ.val ψ.property n‖ ≤ 1024*(1+‖φ‖^2) := by
  apply (sourceRealGapFactor_norm_le_iff (by simp) (by norm_num)
    ψ.val ψ.property n (1024*(1+‖φ‖^2)) (by positivity)).mpr
  intro z hz
  have hdom := sourceStandardRootGapSegment_subset_omittedDomain_of_realType
    (by simp) (by norm_num) ψ.val ψ.property n
  rw [sourceStandardRoot_gapSegment_eq_periodicSegment] at hdom
  have hlim := sourceCriticalRootRatioExtension_le_finite_core (by simp) (by norm_num)
    ψ.val n N hn z (hdom hz) 128
    (fun s hs hsext => sourceM1_real_exterior_product_le_128 w hw ψ φ hφ N hN s n hs hsext hn z hz)
  by_cases hzero : N = 0
  · subst N
    simp only [Nat.cast_zero,neg_zero,Finset.Ioo_self,Finset.prod_empty,norm_one,mul_one] at hlim
    exact hlim.trans (by nlinarith [sq_nonneg ‖φ‖])
  have hcore := sourceM1_real_central_product_sq_le w hw ψ φ hφ N
    (Nat.one_le_iff_ne_zero.mpr hzero) hN n hn z hz
  have hnorm : ‖∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ),
      (canonicalCriticalPoints (by simp) (by norm_num) (periodOnePotential ψ.val)
        (periodOnePotential_mem ψ.val) m-z)/sourceStandardRoot (by simp) (by norm_num) ψ.val m z‖ ≤
      8*(1+‖φ‖^2) := by nlinarith [sq_nonneg (‖φ‖^2),sq_nonneg ‖φ‖]
  linarith

/-- The stronger real bound in exact normalized coordinates, with an inclusive cutoff. -/
theorem sourceM1_real_gapFactor_le_1024_normalized (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : realTypeSourceSubmodule 2) (n : ℤ) (hn : 8*‖a.val‖^2 ≤ 1+|(n:ℝ)|) :
    ‖sourceRealGapFactor (by simp) (by norm_num) (normalizedWeightedSource w a.val)
      (normalizedWeightedSource_realType w a.val a.property) n‖ ≤ 1024*(1+‖a.val‖^2) := by
  let ψ : realTypeSourceSubmodule 2 :=
    ⟨normalizedWeightedSource w a.val,normalizedWeightedSource_realType w a.val a.property⟩
  let φ := normalizedWeightedPeriodOne w a.val
  let K : ℕ := ⌊8*‖a.val‖^2⌋₊
  let N := min n.natAbs K
  have hfloor : (K:ℝ) ≤ 8*‖a.val‖^2 := Nat.floor_le (by positivity)
  have hK : 8*‖a.val‖^2 ≤ 1+(K:ℝ) := by
    have h := Nat.lt_floor_add_one (8*‖a.val‖^2)
    dsimp [K]
    linarith
  have hN : 8*‖a.val‖^2 ≤ 1+(N:ℝ) := by
    by_cases h : n.natAbs ≤ K
    · simpa only [N,min_eq_left h,Nat.cast_natAbs,Int.cast_abs] using hn
    · simpa only [N,min_eq_right (le_of_not_ge h)] using hK
  have hcut : (N:ℝ) ≤ 8*‖a.val‖^2 :=
    (show (N:ℝ) ≤ (K:ℝ) by exact_mod_cast min_le_right n.natAbs K).trans hfloor
  have hb := sourceM1_real_gapFactor_le_1024_at_cutoff w hw ψ φ
    (weightedBaseToPair_normalizedWeightedPeriodOne w a.val) N
    (by simpa only [φ,norm_normalizedWeightedPeriodOne] using hN)
    (by simpa only [φ,norm_normalizedWeightedPeriodOne] using hcut) n (min_le_left _ _)
  simp only [φ,norm_normalizedWeightedPeriodOne] at hb
  exact hb

end NLS.ZakharovShabat
