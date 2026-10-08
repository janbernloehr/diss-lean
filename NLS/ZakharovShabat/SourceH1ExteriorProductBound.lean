import NLS.ZakharovShabat.SourceH1ExteriorFactorBound
import NLS.ZakharovShabat.M1ExteriorGapBudget
import NLS.SequenceSpaces.FiniteReciprocalSquareBudget
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The numerical exterior-product constant in Lemma 28.1

Every finite set of high indices has product norm at most 128. This is
uniform over the entire target gap. No positivity of the cutoff or of
the gap lengths is needed.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace NLS.ZakharovShabat

/-- The gap budget three and reciprocal-square budget 7/2 fit inside 128. -/
theorem exterior_product_exponential_budget :
    Real.exp (Real.sqrt 3*Real.sqrt (7/2)) ≤ 128 := by
  have hx : Real.sqrt 3*Real.sqrt (7/2) ≤ 4 := by
    have he : (Real.sqrt 3*Real.sqrt (7/2))^2 = (21/2:ℝ) := by
      rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7/2)]
      norm_num
    nlinarith [mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (7/2))]
  calc
    _ ≤ Real.exp 4 := Real.exp_le_exp.mpr hx
    _ = (Real.exp 1)^4 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (3:ℝ)^4 := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
    _ ≤ 128 := by norm_num

/-- Cutoff indices satisfy the quadratic localization threshold. -/
theorem exterior_index_localization_threshold (P : ℝ) (N : ℕ)
    (hN : 8*P^2 ≤ 1+(N:ℝ)) (m : ℤ) (hm : N ≤ m.natAbs) :
    8*P^2 ≤ 1+|(m:ℝ)| := by
  have hcast : (N:ℝ) ≤ (m.natAbs:ℝ) := by exact_mod_cast hm
  simp only [Nat.cast_natAbs,Int.cast_abs] at hcast
  linarith

/-- The printed constant 128 for every finite exterior product on real sources. -/
theorem sourceH1_real_exterior_product_le_128 (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) (s : Finset ℤ) (n : ℤ) (hs : n ∉ s)
    (hsext : ∀ m ∈ s, N ≤ m.natAbs) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ.val n) :
    ‖∏ m ∈ s, (canonicalCriticalPoints (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m-z)/
      sourceStandardRoot (by simp) (by norm_num) ψ.val m z‖ ≤ 128 := by
  have heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0 :=
    hφ ▸ periodOnePotential_mem ψ.val
  have hG := M1_canonicalGap_finite_exterior_sq_le_three _
    (SpectralWeight.hasLinearFactor_piSobolev 1 le_rfl) φ heven N hN s hsext
  simp only [hφ] at hG
  exact (sourceH1_real_exterior_product_le_exp_sqrt_budgets ψ φ hφ s n hs
    (fun m hm => exterior_index_localization_threshold ‖φ‖ N hN m (hsext m hm))
    (exterior_index_localization_threshold ‖φ‖ N hN n hn) z hz 3 (7/2) hG
    (ReciprocalSeries.sum_shifted_reciprocal_sq_le s n)).trans exterior_product_exponential_budget

/-- The same finite-product bound for complex sources with the explicit
critical-offset hypothesis required in the almost-real neighborhood. -/
theorem sourceH1_exterior_product_le_128 (ψ : CoeffPair 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) (s : Finset ℤ) (n : ℤ) (hs : n ∉ s)
    (hsext : ∀ m ∈ s, N ≤ m.natAbs) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ n)
    (hc : ∀ m ∈ s,
      ‖canonicalCriticalPoints (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) m-
        canonicalPeriodicMidpoint (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) m‖ ≤
        ‖canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) m‖) :
    ‖∏ m ∈ s, (canonicalCriticalPoints (by simp) (by norm_num)
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/
      sourceStandardRoot (by simp) (by norm_num) ψ m z‖ ≤ 128 := by
  have heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0 :=
    hφ ▸ periodOnePotential_mem ψ
  have hG := M1_canonicalGap_finite_exterior_sq_le_three _
    (SpectralWeight.hasLinearFactor_piSobolev 1 le_rfl) φ heven N hN s hsext
  simp only [hφ] at hG
  apply le_trans (norm_finite_product_le_exp_sqrt_budgets s _
    (fun m => ‖canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m‖)
    (fun m => 1/|((m-n:ℤ):ℝ)|) 3 (7/2) _ hG
    (ReciprocalSeries.sum_shifted_reciprocal_sq_le s n)) exterior_product_exponential_budget
  intro m hms
  have hmn : m ≠ n := fun he => hs (he ▸ hms)
  simpa only [one_div,div_eq_mul_inv,one_mul] using
    sourceH1_exterior_critical_factor_le ψ φ hφ m n hmn
      (exterior_index_localization_threshold ‖φ‖ N hN m (hsext m hms))
      (exterior_index_localization_threshold ‖φ‖ N hN n hn) z hz (hc m hms)

end NLS.ZakharovShabat
