import NLS.SequenceSpaces.Reflection

/-! Complex linear index reflection for any symmetric positive weight. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def symmetricReflection (w : Weight) (_hw : ∀ k, w (-k)=w k) :
    WeightedCoeff w p ≃ₗᵢ[ℂ] WeightedCoeff w p :=
  ((weightIsometry w p).trans Coeff.reflection).trans (weightIsometry w p).symm

theorem symmetricReflection_apply (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : WeightedCoeff w p) (k : ℤ) : (symmetricReflection w hw a).val k=a.val (-k) := by
  change ((w (-k):ℂ)*a.val (-k))/(w k:ℂ)=_
  rw [hw]
  exact mul_div_cancel_left₀ _ (w.complex_ne_zero k)

end NLS.WeightedCoeff
