import NLS.SequenceSpaces.WeightedRealPairProjection

/-! # Complex inclusion of native weighted real pairs

The bounded real linear inclusion preserves every raw coefficient in both
components and is injective at every Banach exponent, including infinity.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.WeightedCoeffPair
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Include native weighted real pairs in their complex weighted pair space. -/
def complexCLM (w : Weight) : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) →L[ℝ]
    WeightedCoeffPair w p :=
  (WithLp.prodContinuousLinearEquiv p ℝ _ _).symm.toContinuousLinearMap.comp
    (((WeightedRealCoeff.complexCLM w p).prodMap (WeightedRealCoeff.complexCLM w p)).comp
      (WithLp.prodContinuousLinearEquiv p ℝ _ _).toContinuousLinearMap)

/-- The first raw weighted sequence is unchanged by complex inclusion. -/
@[simp] theorem complexCLM_fst (w : Weight)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    (complexCLM w z).fst = z.fst.val := rfl

/-- The second raw weighted sequence is unchanged by complex inclusion. -/
@[simp] theorem complexCLM_snd (w : Weight)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    (complexCLM w z).snd = z.snd.val := rfl

/-- Complex inclusion determines a native weighted real pair uniquely. -/
theorem complexCLM_injective (w : Weight) : Function.Injective (complexCLM (p := p) w) := by
  intro x y h
  apply (WithLp.equiv p _).injective
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg (fun a => a.fst) h
  · exact congrArg (fun a => a.snd) h
end NLS.WeightedCoeffPair
