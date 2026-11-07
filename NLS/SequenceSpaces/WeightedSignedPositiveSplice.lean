import NLS.SequenceSpaces.SignedPositiveSplice
import NLS.SequenceSpaces.Weighted

/-! Splice the two positive tails in any even weighted Banach sequence
space. The full raw coefficient formulas retain the original labels. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

def signedPositiveSplice : (WeightedCoeff w p × WeightedCoeff w p) →L[ℂ] WeightedCoeff w p :=
  (weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (Coeff.signedPositiveSplice.comp
      ((weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap.prodMap
        (weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap))

theorem signedPositiveSplice_positive (a b : WeightedCoeff w p) (k : ℤ) (hk : 0 < k) :
    (signedPositiveSplice w p (a,b)).val k = a.val k := by
  change Coeff.signedPositiveSplice (weightIsometry w p a, weightIsometry w p b) k /
    (w k : ℂ) = _
  rw [Coeff.signedPositiveSplice_positive _ _ k hk]
  exact mul_div_cancel_left₀ _ (w.complex_ne_zero k)

theorem signedPositiveSplice_negative (hw : ∀ k : ℤ, w (-k) = w k)
    (a b : WeightedCoeff w p) (k : ℤ) (hk : k < 0) :
    (signedPositiveSplice w p (a,b)).val k = b.val (-k) := by
  change Coeff.signedPositiveSplice (weightIsometry w p a, weightIsometry w p b) k /
    (w k : ℂ) = _
  rw [Coeff.signedPositiveSplice_negative _ _ k hk]
  change (w (-k) : ℂ) * b.val (-k) / (w k : ℂ) = _
  rw [hw k]
  exact mul_div_cancel_left₀ _ (w.complex_ne_zero k)

theorem signedPositiveSplice_zero (a b : WeightedCoeff w p) :
    (signedPositiveSplice w p (a,b)).val 0 = 0 := by
  change Coeff.signedPositiveSplice (weightIsometry w p a, weightIsometry w p b) 0 /
    (w 0 : ℂ) = 0
  rw [Coeff.signedPositiveSplice_zero, zero_div]

end NLS.WeightedCoeff
