import NLS.SequenceSpaces.WeightedPositiveActionDerivatives
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Exact finite sums in the original positive weighted coefficient space -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A sequence supported on finitely many original positive indices is the
finite sum of its literal raw unit directions, in the actual weighted space. -/
theorem eq_sum_positive_single_of_support (a : WeightedCoeff w p) (S : Finset ℕ+)
    (hneg : ∀ j : ℤ, j ≤ 0 → a.val j = 0)
    (htail : ∀ n : ℕ+, n ∉ S → a.val (n : ℤ) = 0) :
    a = ∑ n ∈ S, a.val (n : ℤ) • single (p := p) w (n : ℤ) 1 := by
  have hinj : Function.Injective (fun n : ℕ+ => (n : ℤ)) := by
    intro n k h
    apply Subtype.ext
    change (n : ℤ) = (k : ℤ) at h
    exact Int.ofNat_inj.mp h
  apply Subtype.ext
  funext j
  have heval : (∑ n ∈ S, a.val (n : ℤ) • single (p := p) w (n : ℤ) 1).val j =
      ∑ n ∈ S, a.val (n : ℤ)*(Pi.single (n : ℤ) (1 : ℂ) : ℤ → ℂ) j := by
    change evalCLM w p j (∑ n ∈ S, a.val (n : ℤ) • single (p := p) w (n : ℤ) 1) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [map_smul,evalCLM_apply,single_val]
    rfl
  rw [heval]
  by_cases hj : 0<j
  · let k : ℕ+ := ⟨j.toNat,by omega⟩
    have hk : (k : ℤ) = j := Int.toNat_of_nonneg hj.le
    rw [←hk]
    simp only [Pi.single_apply,hinj.eq_iff]
    by_cases hkS : k ∈ S
    · simp [hkS]
    · simp [hkS,htail k hkS]
  · rw [hneg j (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro n _
    have hnj : j ≠ (n : ℤ) := by
      have hn : (0 : ℤ)<n := by exact_mod_cast n.pos
      omega
    simp only [Pi.single_apply,if_neg hnj,mul_zero]

end NLS.WeightedCoeff
