import NLS.ComplexAnalysis.LocalSinhLinearization
import NLS.SequenceSpaces.SobolevPowerMultiplier
import NLS.SequenceSpaces.WeightedDomination

/-! # Sobolev linearization of small hyperbolic-sine phases

A small inverse-index phase has a one-order smoother inverse-sine remainder at every Banach exponent.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A small inverse-index phase with a weighted hyperbolic-sine realization
has the same Sobolev order, and its inverse-sine remainder gains one order. -/
theorem exists_sobolev_sinh_linearization
    (r : ℝ) (u : ℤ → ℂ) (a : WeightedCoeff (Weight.sobolev r) p)
    (D : ℝ) (hD : 0 ≤ D)
    (ha : ∀ n, a.val n = sinh (u n))
    (hu : ∀ n, ‖u n‖ ≤ 1)
    (hsmall : ∀ n, ‖u n‖ ≤ 2*‖a.val n‖)
    (hdecay : ∀ n : ℤ, (1+|(n:ℝ)|)*‖u n‖ ≤ D) :
    ∃ v : WeightedCoeff (Weight.sobolev r) p,
      ∃ e : WeightedCoeff (Weight.sobolev (r+1)) p,
      (∀ n, v.val n = u n) ∧ (∀ n, e.val n = u n-a.val n) ∧
      ‖v‖ ≤ 2*‖a‖ ∧ ‖e‖ ≤ (2*D)*‖a‖ := by
  classical
  obtain ⟨v,hv,hvn⟩ := exists_of_norm_le _ a u 2 (by norm_num) hsmall
  have herr (n : ℤ) : (1+|(n:ℝ)|)*‖u n-a.val n‖ ≤ (2*D)*‖a.val n‖ := by
    have hquad : ‖u n-a.val n‖ ≤ ‖u n‖^2 := by
      rw [ha n,norm_sub_rev]
      exact NLS.ComplexAnalysis.norm_sinh_sub_self_le_sq (u n) (hu n)
    calc
      _ ≤ (1+|(n:ℝ)|)*‖u n‖^2 := mul_le_mul_of_nonneg_left hquad (by positivity)
      _ = ((1+|(n:ℝ)|)*‖u n‖)*‖u n‖ := by ring
      _ ≤ D*(2*‖a.val n‖) := mul_le_mul (hdecay n) (hsmall n) (norm_nonneg _) hD
      _ = _ := by ring
  let m (n : ℤ) : ℂ := if a.val n = 0 then 0 else (u n-a.val n)/a.val n
  have hm (n : ℤ) : (1+|(n:ℝ)|)*‖m n‖ ≤ 2*D := by
    by_cases hn : a.val n = 0
    · simpa only [m,if_pos hn,norm_zero,mul_zero] using mul_nonneg (by norm_num) hD
    · simp only [m,if_neg hn,norm_div]
      rw [← mul_div_assoc]
      exact (div_le_iff₀ (norm_pos_iff.mpr hn)).mpr (herr n)
  obtain ⟨T,hT,hTn⟩ := exists_sobolev_power_multiplier (p := p) r 1 m (2*D) (by positivity)
    (by intro n; simpa only [Real.rpow_one] using hm n)
  refine ⟨v,T a,hv,?_,hvn,(T.le_opNorm a).trans (mul_le_mul_of_nonneg_right hTn (norm_nonneg _))⟩
  intro n
  rw [hT]
  by_cases hn : a.val n = 0
  · have hu0 : u n = 0 := norm_eq_zero.mp (le_antisymm (by simpa only [hn,norm_zero,mul_zero] using hsmall n) (norm_nonneg _))
    simp [m,hn,hu0]
  · simp only [m,if_neg hn]
    exact div_mul_cancel₀ _ hn

end NLS.WeightedCoeff
