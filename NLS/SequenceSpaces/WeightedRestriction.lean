import NLS.SequenceSpaces.CoefficientRestriction

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.WeightedCoeff

variable {p : ℝ≥0∞} [Fact (1≤p)]

/-- The contractive restriction to an injective set of frequencies,
with exactly the pulled-back original weight. -/
def restrictIndicesCLM (w : Weight) (e : ℤ ↪ ℤ) :
    WeightedCoeff w p →L[ℂ] WeightedCoeff (w.pullback e) p :=
  (weightIsometry (w.pullback e) p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Coeff.restrictIndicesCLM e).comp (weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap)

theorem restrictIndicesCLM_apply (w : Weight) (e : ℤ ↪ ℤ) (a : WeightedCoeff w p) (n : ℤ) :
    (restrictIndicesCLM w e a).val n=a.val (e n) := by
  change ((w (e n) : ℂ)*a.val (e n))/(w (e n) : ℂ)=a.val (e n)
  exact mul_div_cancel_left₀ _ (w.complex_ne_zero (e n))

theorem norm_restrictIndicesCLM_le (w : Weight) (e : ℤ ↪ ℤ) (a : WeightedCoeff w p) :
    ‖restrictIndicesCLM w e a‖≤‖a‖ := by
  change ‖(weightIsometry (w.pullback e) p).symm
    (Coeff.restrictIndices e (weightIsometry w p a))‖≤‖a‖
  rw [(weightIsometry (w.pullback e) p).symm.norm_map]
  exact (Coeff.norm_restrictIndices_le e _).trans_eq ((weightIsometry w p).norm_map a)

end NLS.WeightedCoeff
