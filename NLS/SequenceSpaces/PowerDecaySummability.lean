import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.PSeries

/-! # Summability from inverse-index power decay

The finite initial portion is unrestricted. A common power majorant can
therefore also express uniform summability of tails of a family.
-/

noncomputable section
open Filter
namespace NLS

/-- The two-sided inverse-index power is in ℓp when its p-th power is summable. -/
theorem memlp_inverse_natAbs_rpow (p : ℝ) (hp : 0 < p) (α : ℝ) (hα : 1 < α*p) :
    Memℓp (fun n : ℤ => (n.natAbs : ℝ)^(-α)) (ENNReal.ofReal p) := by
  apply memℓp_gen
  have h := Real.summable_abs_int_rpow hα
  convert h using 1
  ext n
  rw [ENNReal.toReal_ofReal hp.le, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
    ← Real.rpow_mul (by positivity)]
  simp only [Nat.cast_natAbs, Int.cast_abs]
  congr 1
  ring

/-- Eventual domination by an ℓp sequence suffices; arbitrary finite heads are allowed. -/
theorem memlp_of_natAbs_eventual_bound {E : Type*} [NormedAddCommGroup E]
    (p : ℝ) (hp : 0 < p) (f : ℤ → E) (g : ℤ → ℝ)
    (hg : Memℓp g (ENNReal.ofReal p)) (N : ℕ)
    (h : ∀ n : ℤ, N ≤ n.natAbs → ‖f n‖ ≤ g n) :
    Memℓp f (ENNReal.ofReal p) := by
  have hp' : 0 < (ENNReal.ofReal p).toReal := by simpa only [ENNReal.toReal_ofReal hp.le] using hp
  apply memℓp_gen
  apply (hg.summable hp').of_norm_bounded_eventually
  have hlarge : ∀ᶠ n : ℤ in cofinite, N ≤ n.natAbs := by
    apply Filter.eventually_cofinite.mpr
    apply (Finset.Icc (-(N : ℤ)) N).finite_toSet.subset
    intro n hn
    simp only [Set.mem_ofPred_eq, not_le] at hn
    simp only [Finset.mem_coe, Finset.mem_Icc]
    constructor <;> omega
  filter_upwards [hlarge] with n hn
  rw [Real.norm_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow (norm_nonneg _) ((h n hn).trans (Real.le_norm_self _)) hp'.le

end NLS
