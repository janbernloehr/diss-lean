import NLS.Articles.KdVConvexity.OriginalWeightedActionSpace
import NLS.SequenceSpaces.PositiveOneReindex
import NLS.SequenceSpaces.WeightedSingle

/-! The literal positive raw actions of this article in the independently
constructed Hilbert-action physical extension. The bounded map only reindexes
positive labels; the original cubic action weight and coefficients agree. -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.Articles.KdVConvexity

/-- Both papers use the SAME original cubic action weight at every positive label. -/
theorem originalActionWeight_positive (k : ℤ) :
    Weight.sobolev 3 (actionIndexEquiv k : ℤ)=originalActionWeight k := by
  change (1+|((actionIndexEquiv k : ℕ) : ℝ)|)^(3 : ℝ)=(1+(actionIndexEquiv k : ℝ))^3
  rw [abs_of_nonneg (Nat.cast_nonneg (actionIndexEquiv k : ℕ))]
  exact Real.rpow_natCast _ 3

def physicalHilbertActionReindex :
    WeightedCoeff (Weight.sobolev 3) 1 →L[ℂ] OriginalActionSpace :=
  (WeightedCoeff.weightIsometry originalActionWeight 1).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((positiveOneReindexPullCLM actionIndexEquiv).comp
      (WeightedCoeff.weightIsometry (Weight.sobolev 3) 1).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Every raw original positive action is retained without any rescaling. -/
@[simp] theorem physicalHilbertActionReindex_coefficient (a : WeightedCoeff (Weight.sobolev 3) 1) (k : ℤ) :
    (physicalHilbertActionReindex a).val k=a.val (actionIndexEquiv k : ℤ) := by
  change (positiveOneReindexPullCLM actionIndexEquiv
    ((WeightedCoeff.weightIsometry (Weight.sobolev 3) 1) a) k)/(originalActionWeight k : ℂ)=_
  rw [positiveOneReindexPullCLM_apply]
  change ((Weight.sobolev 3 (actionIndexEquiv k : ℤ) : ℂ)*a.val (actionIndexEquiv k : ℤ))/
    (originalActionWeight k : ℂ)=_
  rw [originalActionWeight_positive,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]

/-- Nonnegative original actions map into the same full nonnegative cone. -/
theorem physicalHilbertActionReindex_nonnegative (a : WeightedCoeff (Weight.sobolev 3) 1)
    (ha : a∈WeightedCoeff.nonnegativeLocus (Weight.sobolev 3) 1) :
    physicalHilbertActionReindex a∈WeightedCoeff.nonnegativeLocus originalActionWeight 1 := by
  intro k
  simpa only [physicalHilbertActionReindex_coefficient] using ha (actionIndexEquiv k : ℤ)

/-- The exact unscaled positive action direction is retained by the reindexing. -/
theorem physicalHilbertActionReindex_single (n : ℕ+) (c : ℂ) :
    physicalHilbertActionReindex (WeightedCoeff.single (Weight.sobolev 3) (n : ℤ) c)=
      WeightedCoeff.single originalActionWeight (actionIndexEquiv.symm n) c := by
  apply Subtype.ext
  funext k
  rw [physicalHilbertActionReindex_coefficient]
  simp only [WeightedCoeff.single_val,Pi.single_apply]
  have he : (actionIndexEquiv k : ℤ)=(n : ℤ) ↔ k=actionIndexEquiv.symm n := by
    constructor
    · intro h
      apply actionIndexEquiv.injective
      rw [actionIndexEquiv.apply_symm_apply]
      apply Subtype.ext
      exact Int.ofNat.inj h
    · intro h
      rw [h,actionIndexEquiv.apply_symm_apply]
  simp only [he]

end NLS.Articles.KdVKdV2Frequencies
