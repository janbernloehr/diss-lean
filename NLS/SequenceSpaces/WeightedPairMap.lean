import NLS.SequenceSpaces.PairNorm
import NLS.SequenceSpaces.WeightedMultiplier

/-!
# Componentwise operators in the source's weighted pair norm

A common scalar bound remains the same bound for the finite-exponent pair
sum norm. This avoids losing a factor when constructing the Section 6
projections and complementary inverse.
-/

noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeffPair
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Apply one bounded scalar operator to each physical component. -/
def mapComponents (w v : Weight) (f g : WeightedCoeff w p →L[ℂ] WeightedCoeff v p) :
    WeightedCoeffPair w p →L[ℂ] WeightedCoeffPair v p :=
  (toMax v p).symm.toContinuousLinearMap.comp ((f.prodMap g).comp (toMax w p).toContinuousLinearMap)

@[simp] theorem mapComponents_fst (w v : Weight) (f g : WeightedCoeff w p →L[ℂ] WeightedCoeff v p)
    (a : WeightedCoeffPair w p) : (mapComponents w v f g a).fst = f a.fst := rfl

@[simp] theorem mapComponents_snd (w v : Weight) (f g : WeightedCoeff w p →L[ℂ] WeightedCoeff v p)
    (a : WeightedCoeffPair w p) : (mapComponents w v f g a).snd = g a.snd := rfl

/-- A common component bound is preserved by the exact finite-`p` pair norm. -/
theorem norm_mapComponents_le (hp : p ≠ ⊤) (w v : Weight)
    (f g : WeightedCoeff w p →L[ℂ] WeightedCoeff v p) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ a, ‖f a‖ ≤ C * ‖a‖) (hg : ∀ a, ‖g a‖ ≤ C * ‖a‖) (a : WeightedCoeffPair w p) :
    ‖mapComponents w v f g a‖ ≤ C * ‖a‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  rw [WithLp.prod_norm_eq_add hp0, mapComponents_fst, mapComponents_snd]
  calc
    _ ≤ ((C * ‖a.fst‖) ^ p.toReal + (C * ‖a.snd‖) ^ p.toReal) ^ (1 / p.toReal) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      exact add_le_add (Real.rpow_le_rpow (norm_nonneg _) (hf _) hp0.le)
        (Real.rpow_le_rpow (norm_nonneg _) (hg _) hp0.le)
    _ = C * ‖a‖ := by
      rw [Real.mul_rpow hC (norm_nonneg _), Real.mul_rpow hC (norm_nonneg _), ← mul_add,
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hC, mul_one_div_cancel hp0.ne',
        Real.rpow_one, ← WithLp.prod_norm_eq_add hp0]

end NLS.WeightedCoeffPair
