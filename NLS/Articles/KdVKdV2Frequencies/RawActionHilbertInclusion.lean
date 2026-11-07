import NLS.Articles.KdVConvexity.OriginalWeightedActionSpace

/-! The ORIGINAL raw ell1 actions embed continuously in the existing
positive-index Hilbert action space, without changing any coefficient. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def rawActionHilbertInclusion : Coeff 1 →L[ℂ] ActionSpace :=
  actionUnreindex.toContinuousLinearMap.comp (Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞)≤2))

@[simp] theorem rawActionHilbertInclusion_apply (a : Coeff 1) (n : ℕ+) :
    rawActionHilbertInclusion a n=a (actionIndexEquiv.symm n) := by
  change actionUnreindex (Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞)≤2) a) n=_
  rw [actionUnreindex_apply,Coeff.exponentInclusion_apply]

theorem rawActionHilbertInclusion_nonnegative (a : Coeff 1) (ha : a∈Coeff.nonnegativeLocus 1) :
    rawActionHilbertInclusion a∈positiveQuadrant := by
  intro n
  simpa only [rawActionHilbertInclusion_apply] using ha (actionIndexEquiv.symm n)

theorem rawActionHilbertInclusion_original (b : OriginalActionSpace) :
    rawActionHilbertInclusion (originalActionToCoeffOne b)=originalActionInclusion b := rfl

theorem originalActionInclusion_eq_of_raw_coeffs (b : OriginalActionSpace) (a : Coeff 1)
    (ha : ∀ k : ℤ, (baseActionInclusion (originalActionInclusion b)).val k=a k) :
    originalActionInclusion b=rawActionHilbertInclusion a := by
  ext n
  rw [originalActionInclusion_apply,rawActionHilbertInclusion_apply]
  have h := ha (actionIndexEquiv.symm n)
  simpa only [baseActionInclusion_apply,originalActionInclusion_apply,Equiv.symm_apply_apply] using h

end NLS.Articles.KdVKdV2Frequencies
