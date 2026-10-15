import NLS.ZakharovShabat.SourceIndexedHigherActionBound
import NLS.ZakharovShabat.SourceRealHigherActionPositive
/-! # Real values, odd-level zero detection, and original mean-value comparisons -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceIndexedHigherAction_real (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (k : ℕ) :
    (sourceIndexedHigherAction hp hp1 n k φ.val).im = 0 := by
  rw [sourceIndexedHigherAction_eq_real hp hp1 φ]
  rfl

theorem sourceIndexedHigherAction_even_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ) :
    0 ≤ (sourceIndexedHigherAction hp hp1 n (2*m) φ.val).re := by
  rw [sourceIndexedHigherAction_eq_real hp hp1 φ,ofReal_re]
  exact sourceRealHigherAction_even_nonneg hp hp1 φ n m

/-- Odd printed levels detect precisely the open real periodic gaps. -/
theorem sourceIndexedHigherAction_even_eq_zero_iff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ) :
    sourceIndexedHigherAction hp hp1 n (2*m) φ.val = 0 ↔
      canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
  rw [sourceIndexedHigherAction_eq_real hp hp1 φ,ofReal_eq_zero]
  exact sourceRealHigherAction_even_eq_zero_iff hp hp1 φ n m

/-- Formula (5.6), strengthened to every spectral power and using the original indexed action. -/
theorem sourceIndexedHigherAction_eq_power_mul_action (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (k : ℕ) :
    ∃ ζ ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re,
      sourceIndexedHigherAction hp hp1 n k φ.val = (ζ:ℂ)^k*sourceIndexedAction hp hp1 n φ.val := by
  obtain ⟨ζ,hζ,he⟩ := sourceRealHigherAction_eq_power_mul_action hp hp1 φ n k
  refine ⟨ζ,hζ,?_⟩
  rw [sourceIndexedHigherAction_eq_real hp hp1 φ,he,
    ← sourceIndexedHigherAction_zero hp hp1 n φ.val,sourceIndexedHigherAction_eq_real hp hp1 φ,
    sourceRealHigherAction_zero]
  push_cast
  rfl

namespace SourceSection19Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W U : Set (CoeffPair p)}

/-- Every collapsed complex gap contributes zero at every level on the unchanged domain. -/
theorem indexedHigherAction_of_collapsed (Q : SourceSection19Data hp hp1 W U)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) (k : ℕ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    sourceIndexedHigherAction hp hp1 n k ψ = 0 := by
  obtain ⟨C,hC⟩ := Q.cauchyFamily ψ hψ
  rw [C.indexedHigherAction_eq_boundaryIntegral ψ hC n k]
  simp only [C.gapBoundary_eq_zero_of_collapsed n ψ hgap,mul_zero,intervalIntegral.integral_zero]
end SourceSection19Data
end NLS.ZakharovShabat
