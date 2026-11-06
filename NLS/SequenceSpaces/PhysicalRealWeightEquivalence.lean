import NLS.SequenceSpaces.PhysicalRealCoefficients
import NLS.SequenceSpaces.PhysicalRealUnweightedCoefficients
import NLS.FunctionalAnalysis.SubspaceEquivalence

/-! # Positive symmetric weighting preserves the original physical real form -/
noncomputable section
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS.WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hw : ∀ n, w (-n) = w n)

include hw in
theorem physicalReal_iff_weight (a : WeightedCoeff w p) :
    a ∈ physicalRealSubmodule w p ↔ weightIsometry w p a ∈ Coeff.physicalRealSubmodule p := by
  constructor
  · intro ha n
    change (w n : ℂ)*a.val n = conj ((w (-n) : ℂ)*a.val (-n))
    rw [map_mul,Complex.conj_ofReal,hw n,ha n]
  · intro ha n
    apply mul_left_cancel₀ (w.complex_ne_zero n)
    have hn := ha n
    change (w n : ℂ)*a.val n = conj ((w (-n) : ℂ)*a.val (-n)) at hn
    simpa only [map_mul,Complex.conj_ofReal,hw n] using hn

def physicalRealWeightEquiv : physicalRealSubmodule w p ≃L[ℝ] Coeff.physicalRealSubmodule p := by
  let e : WeightedCoeff w p ≃L[ℝ] Coeff p := NLS.FunctionalAnalysis.complexEquivReal (weightIsometry w p).toContinuousLinearEquiv
  exact @NLS.FunctionalAnalysis.subspaceEquiv ℝ (WeightedCoeff w p) (Coeff p)
    inferInstance inferInstance inferInstance inferInstance inferInstance e
    (physicalRealSubmodule w p) (Coeff.physicalRealSubmodule p) (physicalReal_iff_weight w p hw)

@[simp] theorem physicalRealWeightEquiv_apply (a : physicalRealSubmodule w p) :
    (physicalRealWeightEquiv w p hw a).val = weightIsometry w p a.val := rfl

@[simp] theorem physicalRealWeightEquiv_symm_apply (a : Coeff.physicalRealSubmodule p) :
    ((physicalRealWeightEquiv w p hw).symm a).val = (weightIsometry w p).symm a.val := rfl

end NLS.WeightedCoeff
