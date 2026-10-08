import NLS.ZakharovShabat.SourceRealHigherAction

/-! # Higher-action bounds from localization of the periodic gap

These estimates isolate the use of spectral localization in Chapter 5.
The constants depend only on a containing interval, and the comparison is
valid at every odd level, including collapsed gaps.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Upper comparison from an absolute bound on every point of the gap. -/
theorem sourceRealHigherAction_even_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ) (B : ℝ)
    (hb : ∀ ζ ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re, |ζ| ≤ B) :
    sourceRealHigherAction hp hp1 φ n (2*m) ≤ B^(2*m) * (sourceRealAction hp hp1 φ.val φ.property n).re := by
  obtain ⟨ζ,hζ,he⟩ := sourceRealHigherAction_eq_power_mul_action hp hp1 φ n (2*m)
  rw [he,← pow_abs_two_mul ζ]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg ζ) (hb ζ hζ) _)
    (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 φ.val φ.property n).1

/-- Lower comparison when the gap is uniformly separated from zero. -/
theorem sourceRealHigherAction_even_ge (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ ζ ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re, B ≤ |ζ|) :
    B^(2*m) * (sourceRealAction hp hp1 φ.val φ.property n).re ≤ sourceRealHigherAction hp hp1 φ n (2*m) := by
  obtain ⟨ζ,hζ,he⟩ := sourceRealHigherAction_eq_power_mul_action hp hp1 φ n (2*m)
  rw [he,← pow_abs_two_mul ζ]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB (hb ζ hζ) _)
    (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 φ.val φ.property n).1

/-- A gap localized within radius r of c gives two-sided comparisons at all odd levels. -/
theorem sourceRealHigherAction_even_bounds_of_localization (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ) (c r : ℝ) (hr : r ≤ |c|)
    (hl : c-r ≤ (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re)
    (hu : (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re ≤ c+r) :
    (|c|-r)^(2*m) * (sourceRealAction hp hp1 φ.val φ.property n).re ≤ sourceRealHigherAction hp hp1 φ n (2*m) ∧
      sourceRealHigherAction hp hp1 φ n (2*m) ≤ (|c|+r)^(2*m) * (sourceRealAction hp hp1 φ.val φ.property n).re := by
  have hb (ζ : ℝ) (hζ : ζ ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re) :
      |c|-r ≤ |ζ| ∧ |ζ| ≤ |c|+r := by
    have hd : |ζ-c| ≤ r := abs_le.mpr ⟨by linarith [hζ.1],by linarith [hζ.2]⟩
    have hlow := abs_sub_abs_le_abs_sub c ζ
    rw [abs_sub_comm c ζ] at hlow
    have hhigh := abs_add_le (ζ-c) c
    rw [sub_add_cancel] at hhigh
    constructor <;> linarith
  exact ⟨sourceRealHigherAction_even_ge hp hp1 φ n m (|c|-r) (sub_nonneg.mpr hr) (fun ζ hζ => (hb ζ hζ).1),
    sourceRealHigherAction_even_le hp hp1 φ n m (|c|+r) (fun ζ hζ => (hb ζ hζ).2)⟩

end NLS.ZakharovShabat
