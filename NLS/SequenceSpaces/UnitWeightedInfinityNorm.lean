import NLS.SequenceSpaces.Weighted

/-! Pointwise and supremum norm identities for an actual unit-valued
weight, without identifying transported weight structures by rewriting. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff

theorem norm_apply_le_of_unit_values (w : Weight) (hw : ∀ k, w k=1)
    (a : WeightedCoeff w ⊤) (k : ℤ) : ‖a.val k‖ ≤ ‖a‖ := by
  have h := norm_apply_le w ⊤ a k
  simpa only [hw k,div_one] using h

theorem norm_le_of_unit_values (w : Weight) (hw : ∀ k, w k=1)
    (a : WeightedCoeff w ⊤) (B : ℝ) (hB : 0 ≤ B) (ha : ∀ k, ‖a.val k‖ ≤ B) : ‖a‖ ≤ B := by
  change ‖weightEquiv w ⊤ a‖ ≤ B
  apply lp.norm_le_of_forall_le hB
  intro k
  simpa only [weightEquiv_apply,hw k,Complex.ofReal_one,one_mul] using ha k

end NLS.WeightedCoeff
