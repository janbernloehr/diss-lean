import NLS.SequenceSpaces.Embedding
import NLS.SequenceSpaces.Compact

/-! Compact Hölder multipliers into the Wiener coefficient space.
A symbol at a finite conjugate exponent is approximated in operator
norm by finite-output multipliers. -/
noncomputable section
open Filter
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

theorem isCompactOperator_holderProduct_fixed (hq : q ≠ ⊤) (a : Coeff q) :
    IsCompactOperator ((holderProduct (p := p) (q := q)).flip a) := by
  have ht := (holderProduct (p := p) (q := q)).flip.continuous.continuousAt.tendsto.comp
    (Coeff.tendsto_truncate hq a)
  apply isCompactOperator_of_tendsto ht
  apply Eventually.of_forall
  intro S
  dsimp only [Function.comp_def]
  have he : (holderProduct (p := p) (q := q)).flip (Coeff.truncate S a) =
      (Coeff.truncateCLM (p := 1) S).comp ((holderProduct (p := p) (q := q)).flip a) := by
    apply ContinuousLinearMap.ext
    intro b
    ext k
    change b k * (Coeff.truncate S a) k = Coeff.truncate S _ k
    simp only [Coeff.truncate_apply]
    split_ifs
    · rfl
    · exact mul_zero _
  rw [he]
  exact (Coeff.isCompactOperator_truncateCLM (p := 1) S).comp_clm _

def weightedHilbertWienerInclusion (w v : Weight)
    (h : Memℓp (fun k => (v k : ℂ) / (w k : ℂ)) 2) :
    WeightedCoeff w 2 →L[ℂ] WeightedCoeff v 1 :=
  (weightIsometry v 1).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((holderProduct (p := 2) (q := 2)).flip ⟨_,h⟩).comp
      (weightIsometry w 2).toContinuousLinearEquiv.toContinuousLinearMap)

theorem weightedHilbertWienerInclusion_apply (w v : Weight)
    (h : Memℓp (fun k => (v k : ℂ) / (w k : ℂ)) 2)
    (a : WeightedCoeff w 2) (k : ℤ) :
    (weightedHilbertWienerInclusion w v h a).val k = a.val k := by
  change (((w k : ℂ) * a.val k) * ((v k : ℂ) / (w k : ℂ))) / (v k : ℂ) = _
  field_simp [w.complex_ne_zero k, v.complex_ne_zero k]

theorem isCompactOperator_weightedHilbertWienerInclusion (w v : Weight)
    (h : Memℓp (fun k => (v k : ℂ) / (w k : ℂ)) 2) :
    IsCompactOperator (weightedHilbertWienerInclusion w v h) :=
  ((isCompactOperator_holderProduct_fixed (p := 2) (q := 2) (by norm_num) ⟨_,h⟩).comp_clm
    (weightIsometry w 2).toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      (weightIsometry v 1).symm.toContinuousLinearEquiv.toContinuousLinearMap

end NLS.WeightedCoeff
