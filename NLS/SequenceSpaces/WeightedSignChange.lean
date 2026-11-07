import NLS.SequenceSpaces.Weighted
import NLS.SequenceSpaces.SignChange

/-! Arbitrary fixed output signs act isometrically on the EXACT raw
weighted space, preserving the original unweighted coefficients. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1≤p)]

def signChangeCLM (w : Weight) (e : ℤ → Bool) : WeightedCoeff w p →L[ℂ] WeightedCoeff w p :=
  (weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Coeff.signChange e).comp (weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap)

theorem signChangeCLM_apply (w : Weight) (e : ℤ → Bool) (A : WeightedCoeff w p) (j : ℤ) :
    (signChangeCLM w e A).val j=if e j then -A.val j else A.val j := by
  change (Coeff.signChange e (weightIsometry w p A) j)/(w j:ℂ)=_
  rw [Coeff.signChange_apply]
  change (if e j then -((w j:ℂ)*A.val j) else (w j:ℂ)*A.val j)/(w j:ℂ)=_
  cases e j <;> simp only [Bool.false_eq_true,↓reduceIte,neg_div,
    mul_div_cancel_left₀ _ (w.complex_ne_zero j)]

theorem norm_signChangeCLM (w : Weight) (e : ℤ → Bool) (A : WeightedCoeff w p) :
    ‖signChangeCLM w e A‖=‖A‖ := by
  change ‖(weightIsometry w p).symm (Coeff.signChange e (weightIsometry w p A))‖=‖A‖
  rw [(weightIsometry w p).symm.norm_map,Coeff.norm_signChange,(weightIsometry w p).norm_map]

end NLS.WeightedCoeff
