import NLS.SequenceSpaces.WeightedMultiplier

/-! # Squared symbols and doubled Sobolev order

Squaring an order-s decaying symbol sends an unweighted sequence into the actual order-2s weighted space.
-/

noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Squaring a symbol with order-s pointwise decay transfers an unweighted
lp sequence into the actual order-2s Sobolev space. -/
theorem exists_sobolev_square_mul (s : ℕ) (g : ℤ → ℂ) (q : Coeff p)
    (R : ℝ) (hg : ∀ n : ℤ, (1+|(n:ℝ)|)^s*‖g n‖ ≤ R) :
    ∃ b : WeightedCoeff (Weight.sobolev ((2*s:ℕ):ℝ)) p,
      (∀ n, b.val n = (g n)^2*q n) ∧ ‖b‖ ≤ R^2*‖q‖ := by
  let w := Weight.sobolev 0
  let v := Weight.sobolev ((2*s:ℕ):ℝ)
  let a : WeightedCoeff w p := (weightIsometry w p).symm q
  have ha (n : ℤ) : a.val n = q n := by
    change q n/(w n:ℂ) = q n
    simp [w]
  have hm (n : ℤ) : v n*‖(g n)^2‖ ≤ R^2*w n := by
    simp only [v,w,Weight.sobolev_apply,Real.rpow_natCast,Real.rpow_zero,mul_one,norm_pow]
    calc
      _ = ((1+|(n:ℝ)|)^s*‖g n‖)^2 := by
        rw [mul_comm 2 s,pow_mul,mul_pow]
      _ ≤ R^2 := pow_le_pow_left₀ (by positivity) (hg n) 2
  refine ⟨weightedMultiplier w v (fun n => (g n)^2) (R^2) hm a,?_,?_⟩
  · intro n
    rw [weightedMultiplier_apply,ha]
  · simpa only [a,LinearIsometryEquiv.norm_map] using
      norm_weightedMultiplier_le w v (fun n => (g n)^2) (R^2) (sq_nonneg R) hm a

end NLS.WeightedCoeff
