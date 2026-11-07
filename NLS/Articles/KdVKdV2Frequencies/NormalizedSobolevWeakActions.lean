import NLS.Articles.KdVKdV2Frequencies.StrongWeakFrequencyCompatibility
import NLS.Articles.KdVKdV2Frequencies.Theorem12WeakEndpoint

/-! The normalized intermediate action cone includes continuously in
the normalized weak cone. Weights always use the original positive
frequency label, rather than its integer enumeration. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def enumeratedSobolevActionWeight (α : ℝ) : Weight :=
  ⟨fun k => Weight.sobolev α (actionIndexEquiv k : ℤ),fun k => (Weight.sobolev α).positive (actionIndexEquiv k : ℤ)⟩

theorem baseActionWeight_eq_sobolev (k : ℤ) :
    baseActionWeight k=Weight.sobolev (-1) (actionIndexEquiv k : ℤ) := by
  simp only [baseActionWeight,Weight.sobolev_apply,Real.rpow_neg_one,Int.cast_natCast,
    abs_of_pos (by exact_mod_cast (actionIndexEquiv k).pos : (0 : ℝ)<actionIndexEquiv k)]

theorem enumeratedSobolevActionWeight_base_le (α : ℝ) (hα : -1≤α) (k : ℤ) :
    baseActionWeight k≤enumeratedSobolevActionWeight α k := by
  rw [baseActionWeight_eq_sobolev]
  exact Weight.sobolev_mono hα _

def normalizedSobolevWeakActionInclusion (α : ℝ) (hα : -1≤α) : Coeff 1 →L[ℂ] Coeff 1 :=
  baseActionNormalization.toContinuousLinearMap.comp
    ((WeightedCoeff.inclusionCLM (enumeratedSobolevActionWeight α) baseActionWeight (enumeratedSobolevActionWeight_base_le α hα)).comp
      (WeightedCoeff.weightIsometry (enumeratedSobolevActionWeight α) 1).symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem normalizedSobolevWeakActionInclusion_apply (α : ℝ) (hα : -1≤α)
    (a : Coeff 1) (k : ℤ) :
    normalizedSobolevWeakActionInclusion α hα a k=
      (baseActionWeight k : ℂ)*(a k/(Weight.sobolev α (actionIndexEquiv k : ℤ) : ℂ)) := by
  change (baseActionWeight k : ℂ)*(WeightedCoeff.inclusionCLM _ _ (enumeratedSobolevActionWeight_base_le α hα)
    ((WeightedCoeff.weightIsometry (enumeratedSobolevActionWeight α) 1).symm a)).val k=_
  rw [WeightedCoeff.inclusionCLM_apply]
  rfl

theorem normalizedSobolevWeakActionInclusion_nonnegative (α : ℝ) (hα : -1≤α)
    (a : Coeff 1) (ha : a∈Coeff.nonnegativeLocus 1) :
    normalizedSobolevWeakActionInclusion α hα a∈Coeff.nonnegativeLocus 1 := by
  intro k
  rw [normalizedSobolevWeakActionInclusion_apply]
  simp only [Complex.mul_im,Complex.mul_re,Complex.div_im,Complex.div_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,add_zero,sub_zero,(ha k).1]
  have hbase := (baseActionWeight.positive k).le
  have hw := ((Weight.sobolev α).positive (actionIndexEquiv k : ℤ)).le
  have ha0 := (ha k).2
  constructor
  · ring
  · exact mul_nonneg hbase (add_nonneg (div_nonneg (mul_nonneg ha0 hw) (Complex.normSq_nonneg _)) (by simp))

end NLS.Articles.KdVKdV2Frequencies
