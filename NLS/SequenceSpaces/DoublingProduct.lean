import NLS.SequenceSpaces.Embedding

/-!
# Products at doubled exponents

Hölder maps `ℓq × ℓq` to `ℓp` when `q=2p`. The square product has norm
exactly `‖a‖²`; this identity allows the Cotlar argument to be iterated.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderTriple q p]

private theorem norm_complex_mul_le : ‖ContinuousLinearMap.mul ℂ ℂ‖ ≤ (1 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using ContinuousLinearMap.opNorm_mul_apply_le ℂ ℂ x

/-- Pointwise multiplication from the doubled exponent into the original exponent. -/
def doublingProduct : Coeff q →L[ℂ] Coeff q →L[ℂ] Coeff p :=
  lp.holderL (p := q) (q := q) p (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
    (K := 1) (fun _ => norm_complex_mul_le)

@[simp] theorem doublingProduct_apply (a b : Coeff q) (n : ℤ) :
    doublingProduct (p := p) a b n = a n * b n := rfl

theorem norm_doublingProduct_le (a b : Coeff q) :
    ‖doublingProduct (p := p) a b‖ ≤ ‖a‖ * ‖b‖ := by
  have hn : ‖doublingProduct (p := p) (q := q)‖ ≤ 1 :=
    lp.norm_holderL_le p (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
      (K := 1) (fun _ => norm_complex_mul_le)
  exact (doublingProduct (p := p) a).le_of_opNorm_le
    (by simpa using (doublingProduct (p := p) (q := q)).le_of_opNorm_le hn a) b

/-- Squaring converts the doubled-exponent norm into the square of that norm. -/
theorem norm_doublingProduct_self (hp : 0 < p.toReal) (hq : q.toReal = 2 * p.toReal)
    (a : Coeff q) : ‖doublingProduct (p := p) a a‖ = ‖a‖ ^ 2 := by
  have hqpos : 0 < q.toReal := by rw [hq]; positivity
  apply (Real.rpow_left_inj (norm_nonneg _) (sq_nonneg _) hp.ne').mp
  rw [lp.norm_rpow_eq_tsum hp]
  have he : (∑' n : ℤ, ‖doublingProduct (p := p) a a n‖ ^ p.toReal) =
      ∑' n : ℤ, ‖a n‖ ^ q.toReal := by
    apply tsum_congr
    intro n
    rw [doublingProduct_apply, norm_mul, ← pow_two, ← Real.rpow_two,
      ← Real.rpow_mul (norm_nonneg _), ← hq]
  rw [he, ← lp.norm_rpow_eq_tsum hqpos]
  rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _), ← hq]

end NLS.Coeff
