import NLS.Articles.KdVKdV2Frequencies.NormalizedSobolevWeakActions
import NLS.SequenceSpaces.WeightedReciprocalKernel
import NLS.SequenceSpaces.PositiveReindex

/-! Original Hilbert actions include continuously in every intermediate
weighted ell1 order below -1/2. The literal physical frequency label sets
the weight, and the weak-action inclusion commutes coefficientwise. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def intermediateHilbertWeightPacket (α : ℝ) (hα : α< -1/2) : Coeff 2 :=
  positiveReindexPull actionIndexEquiv ⟨fun n => (Weight.sobolev α n : ℂ),by
    have hm : Memℓp (fun n : ℤ => (Weight.sobolev α n : ℂ)) 2 := by
      simpa only [neg_neg] using Weight.memlp_negative_sobolev (p := 2) (by norm_num) (-α)
        (by norm_num;linarith)
    exact memℓp_gen (hm.summable (by norm_num))⟩

def hilbertIntermediateActionInclusion (α : ℝ) (hα : α< -1/2) : Coeff 2 →L[ℂ] Coeff 1 :=
  Coeff.holderProduct (q := 1) (intermediateHilbertWeightPacket α hα)

@[simp] theorem hilbertIntermediateActionInclusion_apply (α : ℝ) (hα : α< -1/2)
    (a : Coeff 2) (k : ℤ) :
    hilbertIntermediateActionInclusion α hα a k=
      (Weight.sobolev α (actionIndexEquiv k : ℤ) : ℂ)*a k := rfl

theorem hilbertIntermediateActionInclusion_nonnegative (α : ℝ) (hα : α< -1/2)
    (a : Coeff 2) (ha : a∈Coeff.nonnegativeLocus 2) :
    hilbertIntermediateActionInclusion α hα a∈Coeff.nonnegativeLocus 1 := by
  intro k
  rw [hilbertIntermediateActionInclusion_apply]
  constructor
  · simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,(ha k).1,mul_zero,zero_mul,add_zero]
  · simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using
      mul_nonneg ((Weight.sobolev α).positive (actionIndexEquiv k : ℤ)).le (ha k).2

theorem hilbertIntermediateActionInclusion_weak (α : ℝ) (hα : α< -1/2) (hα0 : -1≤α)
    (a : Coeff 2) :
    normalizedSobolevWeakActionInclusion α hα0 (hilbertIntermediateActionInclusion α hα a)=
      weakActionEnumeration (hilbertWeakActions (actionUnreindex a)) := by
  ext k
  rw [normalizedSobolevWeakActionInclusion_apply,hilbertIntermediateActionInclusion_apply,
    mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _),weakActionEnumeration_hilbert]
  change (baseActionWeight k : ℂ)*a k=
    (baseActionWeight k : ℂ)*(baseActionInclusion (actionUnreindex a)).val k
  rw [baseActionInclusion_apply,actionUnreindex_apply,Equiv.symm_apply_apply]

end NLS.Articles.KdVKdV2Frequencies
