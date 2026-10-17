import NLS.SequenceSpaces.WeightedRealCoeff
import NLS.SequenceSpaces.PairNorm

/-! # Real projection in the native weighted pair norm

The target is the original weighted real sequence pair, with the same
WithLp norm and raw coefficient values.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS
namespace WeightedCoeffPair
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Continuous real-part projection onto native weighted real pairs. -/
def reCLM (w : Weight) : WeightedCoeffPair w p →L[ℝ]
    WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) :=
  (WithLp.prodContinuousLinearEquiv p ℝ _ _).symm.toContinuousLinearMap.comp
    (((WeightedCoeff.reCLM w p).prodMap (WeightedCoeff.reCLM w p)).comp
      (WithLp.prodContinuousLinearEquiv p ℝ _ _).toContinuousLinearMap)

private theorem reCLM_eq_of_coordinates (w : Weight) (a : WeightedCoeff w p)
    (b : WeightedRealCoeff w p) (h : ∀ n, a.val n = b.val.val n) :
    WeightedCoeff.reCLM w p a = b := by
  have he : a = b.val := Subtype.ext (funext h)
  rw [he]
  apply Subtype.ext
  exact WeightedCoeff.complexCLM_reCLM w p b.val
    ((WeightedCoeff.mem_realSubmodule_iff w p b.val).mp b.property)

/-- Real coefficient agreement identifies the entire projected pair. -/
theorem reCLM_pair_eq_of_coordinates (w : Weight) (a : WeightedCoeffPair w p)
    (b : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p))
    (h : ∀ n, a.fst.val n = b.fst.val.val n ∧ a.snd.val n = b.snd.val.val n) :
    reCLM w a = b := by
  apply (WithLp.equiv p _).injective
  apply Prod.ext
  · exact reCLM_eq_of_coordinates w a.fst b.fst (fun n => (h n).1)
  · exact reCLM_eq_of_coordinates w a.snd b.snd (fun n => (h n).2)
end WeightedCoeffPair

end NLS
