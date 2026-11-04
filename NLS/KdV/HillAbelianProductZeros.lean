import NLS.KdV.HillAbelianProductContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillGapRootEnergyFactor_denominator_ne_zero (k : ℕ) :
    (freeHillValue (k+1 : ℕ) : ℂ) ≠ 0 := by
  apply ofReal_ne_zero.mpr
  unfold freeHillValue
  exact mul_ne_zero (pow_ne_zero _ Real.pi_ne_zero)
    (pow_ne_zero _ (by exact_mod_cast (show ((k+1 : ℕ) : ℤ) ≠ 0 by omega)))

theorem hillAbelianNumeratorProduct_ne_zero_iff
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) (n : ℕ) (z : ℂ) :
    hillAbelianNumeratorProduct σ n z ≠ 0 ↔
      ∀ k : ℕ, k+1 ≠ n → (σ k : ℂ) ≠ z := by
  have hs := summable_norm_hillAbelianNumeratorFactor_sub_one q hq hr σ hσ n z
  have he (k : ℕ) : 1+(hillAbelianNumeratorFactor σ n k z-1) =
      hillAbelianNumeratorFactor σ n k z := by ring
  have hp := tprod_one_add_ne_zero_iff (fun k => hillAbelianNumeratorFactor σ n k z-1) hs
  simp only [he] at hp
  change (∏' k, hillAbelianNumeratorFactor σ n k z) ≠ 0 ↔ _
  rw [hp]
  constructor
  · intro h k hk hz
    have hh := h k
    simp only [hillAbelianNumeratorFactor,if_neg hk,hillGapRootEnergyFactor,hz,
      sub_self,zero_div,ne_eq,not_true_eq_false] at hh
  · intro h k
    unfold hillAbelianNumeratorFactor
    split_ifs with hk
    · norm_num
    · exact div_ne_zero (sub_ne_zero.mpr (h k hk))
        (hillGapRootEnergyFactor_denominator_ne_zero k)

theorem hillAbelianNumeratorProduct_zero_iff
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) (n : ℕ) (z : ℂ) :
    hillAbelianNumeratorProduct σ n z = 0 ↔
      ∃ k : ℕ, k+1 ≠ n ∧ (σ k : ℂ) = z := by
  have h := not_congr (hillAbelianNumeratorProduct_ne_zero_iff q hq hr σ hσ n z)
  simpa only [not_not,not_forall,exists_prop] using h

theorem hillAbelianPsiCandidate_zero_iff
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    hillAbelianPsiCandidate σ n z = 0 ↔
      ∃ k : ℕ, k+1 ≠ n ∧ (σ k : ℂ) = z := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hp : (2 : ℂ)/((n : ℂ)*Real.pi) ≠ 0 := div_ne_zero (by norm_num)
    (mul_ne_zero hn0 (ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [hillAbelianPsiCandidate,mul_eq_zero]
  simp only [hp,false_or]
  exact hillAbelianNumeratorProduct_zero_iff q hq hr σ hσ n z

end NLS.KdV
