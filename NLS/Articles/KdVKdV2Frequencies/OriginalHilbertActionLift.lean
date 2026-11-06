import NLS.Articles.KdVKdV2Frequencies.PhysicalHilbertActionReindex
import NLS.SequenceSpaces.PositiveOneExtension
import NLS.SequenceSpaces.WeightedPositiveActionDerivatives

/-! Exact positive-index extension of the shared original weighted actions,
and the literal normalized weak-action inclusion of positive Hilbert actions.
Both maps retain the original raw actions and vanish at nonpositive slots. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Articles.KdVConvexity
namespace NLS.Articles.KdVKdV2Frequencies

/-- Recover the original positive cubic-weight actions from their positive
label enumeration. No coefficient, action weight or amplitude is altered. -/
def originalHilbertActionLift : OriginalActionSpace →L[ℂ] WeightedCoeff (Weight.sobolev 3) 1 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev 3) 1).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (positiveOneExtendIsometry actionIndexEquiv |>.toContinuousLinearMap |>.comp
      (WeightedCoeff.weightIsometry originalActionWeight 1).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem originalHilbertActionLift_index (b : OriginalActionSpace) (k : ℤ) :
    (originalHilbertActionLift b).val (actionIndexEquiv k : ℤ)=b.val k := by
  change positiveOneExtendFunction actionIndexEquiv
    ((WeightedCoeff.weightIsometry originalActionWeight 1) b) (positiveIndexInjection actionIndexEquiv k)/
      (Weight.sobolev 3 (actionIndexEquiv k : ℤ) : ℂ)=_
  rw [positiveOneExtendFunction_index]
  change (originalActionWeight k : ℂ)*b.val k/(Weight.sobolev 3 (actionIndexEquiv k : ℤ) : ℂ)=_
  rw [originalActionWeight_positive,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]

@[simp] theorem originalHilbertActionLift_nonpositive (b : OriginalActionSpace) (j : ℤ) (hj : j≤0) :
    (originalHilbertActionLift b).val j=0 := by
  change positiveOneExtendFunction actionIndexEquiv _ j/(Weight.sobolev 3 j : ℂ)=0
  rw [positiveOneExtendFunction,dif_neg (by omega),zero_div]

theorem physicalHilbertActionReindex_lift (b : OriginalActionSpace) :
    physicalHilbertActionReindex (originalHilbertActionLift b)=b := by
  apply Subtype.ext
  funext k
  rw [physicalHilbertActionReindex_coefficient,originalHilbertActionLift_index]

/-- The complete nonnegative enumerated cone gives original positive actions,
including arbitrary infinite support and all closed coordinates. -/
theorem originalHilbertActionLift_positive (b : OriginalActionSpace)
    (hb : b∈WeightedCoeff.nonnegativeLocus originalActionWeight 1) :
    originalHilbertActionLift b∈WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1 := by
  refine ⟨?_,originalHilbertActionLift_nonpositive b⟩
  intro j
  by_cases hj : 0<j
  · let n : ℕ+ := ⟨j.toNat,by omega⟩
    let k := actionIndexEquiv.symm n
    have he : (actionIndexEquiv k : ℤ)=j := by
      rw [Equiv.apply_symm_apply]
      exact Int.toNat_of_nonneg hj.le
    rw [←he,originalHilbertActionLift_index]
    exact hb k
  · rw [originalHilbertActionLift_nonpositive b j (by omega)]
    exact ⟨rfl,le_rfl⟩

/-- Every original native positive action point is retained by the round trip. -/
theorem originalHilbertActionLift_reindex
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1) :
    originalHilbertActionLift (physicalHilbertActionReindex a.val)=a.val := by
  apply Subtype.ext
  funext j
  by_cases hj : 0<j
  · let n : ℕ+ := ⟨j.toNat,by omega⟩
    let k := actionIndexEquiv.symm n
    have he : (actionIndexEquiv k : ℤ)=j := by
      rw [Equiv.apply_symm_apply]
      exact Int.toNat_of_nonneg hj.le
    rw [←he,originalHilbertActionLift_index,physicalHilbertActionReindex_coefficient]
  · rw [originalHilbertActionLift_nonpositive _ j (by omega),a.property.2 j (by omega)]

/-- The positive Hilbert actions in the SAME original normalized weak l1
space used by the actual weak inverse and frequency descent. -/
def hilbertWeakActions : ActionSpace →L[ℂ] Coeff 1 :=
  (positiveOneExtendIsometry actionIndexEquiv).toContinuousLinearMap.comp
    ((WeightedCoeff.weightIsometry baseActionWeight 1).toContinuousLinearEquiv.toContinuousLinearMap.comp
      baseActionInclusion)

@[simp] theorem hilbertWeakActions_index (a : ActionSpace) (k : ℤ) :
    hilbertWeakActions a (actionIndexEquiv k : ℤ)=(baseActionWeight k : ℂ)*a (actionIndexEquiv k) := by
  change positiveOneExtendFunction actionIndexEquiv _ (positiveIndexInjection actionIndexEquiv k)=_
  rw [positiveOneExtendFunction_index]
  change (baseActionWeight k : ℂ)*(baseActionInclusion a).val k=_
  rw [baseActionInclusion_apply]

@[simp] theorem hilbertWeakActions_nonpositive (a : ActionSpace) (j : ℤ) (hj : j≤0) :
    hilbertWeakActions a j=0 := by
  change positiveOneExtendFunction actionIndexEquiv _ j=0
  rw [positiveOneExtendFunction,dif_neg (by omega)]

/-- The weak weight is exactly (1+n)^-1 at every original positive index. -/
theorem weakActionWeight_positive (k : ℤ) :
    Weight.sobolev (-1) (actionIndexEquiv k : ℤ)=baseActionWeight k := by
  change (1+|((actionIndexEquiv k : ℕ) : ℝ)|)^(-1 : ℝ)=(1+(actionIndexEquiv k : ℝ))⁻¹
  rw [abs_of_nonneg (Nat.cast_nonneg (actionIndexEquiv k : ℕ)),Real.rpow_neg_one]

/-- The complete nonnegative Hilbert cone maps to nonnegative weak actions. -/
theorem hilbertWeakActions_nonnegative (a : ActionSpace) (ha : a∈positiveQuadrant) :
    hilbertWeakActions a∈Coeff.nonnegativeLocus 1 := by
  intro j
  by_cases hj : 0<j
  · let n : ℕ+ := ⟨j.toNat,by omega⟩
    let k := actionIndexEquiv.symm n
    have he : (actionIndexEquiv k : ℤ)=j := by
      rw [Equiv.apply_symm_apply]
      exact Int.toNat_of_nonneg hj.le
    rw [←he,hilbertWeakActions_index]
    simp only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero,(ha (actionIndexEquiv k)).1,mul_zero,
      mul_re,sub_zero]
    exact ⟨trivial,mul_nonneg (baseActionWeight.positive k).le (ha (actionIndexEquiv k)).2⟩
  · rw [hilbertWeakActions_nonpositive a j (by omega)]
    exact ⟨rfl,le_rfl⟩

end NLS.Articles.KdVKdV2Frequencies
