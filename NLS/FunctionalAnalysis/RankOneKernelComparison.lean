import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Basic

/-! Operator-norm comparison of complex rank-one kernels, retaining
both their actual functional and their bilinear normalization denominator. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Exact comparison for normalized rank-one operators between DIFFERENT
input and output normed spaces. It applies in particular to L2-to-uniform
spectral kernels; the normalization is complex bilinear. -/
theorem norm_rankOneKernel_sub_le (ell k : E →L[ℂ] ℂ) (v w : F)
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖(a⁻¹ • ell).smulRight v-(b⁻¹ • k).smulRight w‖ ≤
      (‖ell‖/‖a‖)*‖v-w‖+
        (‖ell-k‖/‖a‖+‖a-b‖*‖k‖/(‖a‖*‖b‖))*‖w‖ := by
  have he : (a⁻¹ • ell).smulRight v-(b⁻¹ • k).smulRight w =
      (a⁻¹ • ell).smulRight (v-w)+
        (a⁻¹ • (ell-k)+(a⁻¹-b⁻¹) • k).smulRight w := by
    apply ContinuousLinearMap.ext
    intro x
    change (a⁻¹*ell x) • v-(b⁻¹*k x) • w =
      (a⁻¹*ell x) • (v-w)+(a⁻¹*(ell x-k x)+(a⁻¹-b⁻¹)*k x) • w
    module
  have hinv : ‖a⁻¹-b⁻¹‖ = ‖a-b‖/(‖a‖*‖b‖) := by
    rw [inv_sub_inv' ha hb,norm_mul,norm_mul,norm_inv,norm_inv,norm_sub_rev]
    ring
  rw [he]
  calc
    _ ≤ ‖(a⁻¹ • ell).smulRight (v-w)‖+
        ‖(a⁻¹ • (ell-k)+(a⁻¹-b⁻¹) • k).smulRight w‖ := norm_add_le _ _
    _ = (‖a‖⁻¹*‖ell‖)*‖v-w‖+
        ‖a⁻¹ • (ell-k)+(a⁻¹-b⁻¹) • k‖*‖w‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply,ContinuousLinearMap.norm_smulRight_apply,
        norm_smul,norm_inv]
    _ ≤ (‖a‖⁻¹*‖ell‖)*‖v-w‖+
        (‖a‖⁻¹*‖ell-k‖+(‖a-b‖/(‖a‖*‖b‖))*‖k‖)*‖w‖ := by
      gcongr
      exact (norm_add_le _ _).trans_eq (by rw [norm_smul,norm_smul,norm_inv,hinv])
    _ = _ := by ring

end NLS.FunctionalAnalysis
