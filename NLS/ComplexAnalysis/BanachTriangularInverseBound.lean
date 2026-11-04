import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! An explicit two-sided inverse and norm bound for a Banach implicit
function's triangular joint derivative, in terms of the ACTUAL partial
inverse and full derivative norm. -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup P] [NormedSpace ℂ P]

def banachTriangularInverseCLM (A : (E × P) →L[ℂ] E) (e : E ≃L[ℂ] E) : (E × P) →L[ℂ] (E × P) :=
  (e.symm.toContinuousLinearMap.comp ((ContinuousLinearMap.fst ℂ E P)-
    (A.comp (ContinuousLinearMap.inr ℂ E P)).comp (ContinuousLinearMap.snd ℂ E P))).prod
      (ContinuousLinearMap.snd ℂ E P)

theorem banachTriangularInverseCLM_apply (A : (E × P) →L[ℂ] E) (e : E ≃L[ℂ] E) (t : E × P) :
    banachTriangularInverseCLM A e t = (e.symm (t.1-A (0,t.2)),t.2) := rfl

theorem banachTriangular_derivative_decompose (A : (E × P) →L[ℂ] E) (e : E ≃L[ℂ] E)
    (he : e.toContinuousLinearMap = A.comp (ContinuousLinearMap.inl ℂ E P)) (t : E × P) :
    A t = e t.1+A (0,t.2) := by
  have ht : t = (t.1,(0:P))+(0,t.2) := by ext <;> simp
  calc
    A t = A ((t.1,(0:P))+(0,t.2)) := congrArg A ht
    _ = A (t.1,0)+A (0,t.2) := A.map_add _ _
    _ = e t.1+A (0,t.2) := by
      have hx : e t.1 = A (t.1,0) := congrArg (fun J : E →L[ℂ] E => J t.1) he
      rw [← hx]

theorem banachTriangular_derivative_comp_inverse (A : (E × P) →L[ℂ] E) (e : E ≃L[ℂ] E)
    (he : e.toContinuousLinearMap = A.comp (ContinuousLinearMap.inl ℂ E P)) :
    (A.prod (ContinuousLinearMap.snd ℂ E P)).comp (banachTriangularInverseCLM A e) = ContinuousLinearMap.id ℂ (E × P) := by
  apply ContinuousLinearMap.ext
  intro t
  change (A (banachTriangularInverseCLM A e t),(banachTriangularInverseCLM A e t).2) = t
  rw [banachTriangularInverseCLM_apply,banachTriangular_derivative_decompose A e he]
  simp only [ContinuousLinearEquiv.apply_symm_apply,sub_add_cancel,Prod.mk.eta]

theorem banachTriangular_inverse_comp_derivative (A : (E × P) →L[ℂ] E) (e : E ≃L[ℂ] E)
    (he : e.toContinuousLinearMap = A.comp (ContinuousLinearMap.inl ℂ E P)) :
    (banachTriangularInverseCLM A e).comp (A.prod (ContinuousLinearMap.snd ℂ E P)) = ContinuousLinearMap.id ℂ (E × P) := by
  apply ContinuousLinearMap.ext
  intro t
  change banachTriangularInverseCLM A e (A t,t.2) = t
  rw [banachTriangularInverseCLM_apply,banachTriangular_derivative_decompose A e he]
  simp only [add_sub_cancel_right,ContinuousLinearEquiv.symm_apply_apply,Prod.mk.eta]

theorem norm_banachTriangularInverseCLM_le (A : (E × P) →L[ℂ] E) (e : E ≃L[ℂ] E)
    (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C) (he : ‖e.symm.toContinuousLinearMap‖ ≤ M) (hA : ‖A‖ ≤ C) :
    ‖banachTriangularInverseCLM A e‖ ≤ M*(1+C)+1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro t
  rw [banachTriangularInverseCLM_apply]
  change max ‖e.symm (t.1-A (0,t.2))‖ ‖t.2‖ ≤ (M*(1+C)+1)*‖t‖
  apply max_le
  · have hAv : ‖A (0,t.2)‖ ≤ C*‖t.2‖ := by simpa only [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)] using A.le_of_opNorm_le hA (0,t.2)
    calc
      _ ≤ M*‖t.1-A (0,t.2)‖ := e.symm.toContinuousLinearMap.le_of_opNorm_le he _
      _ ≤ M*(‖t.1‖+C*‖t.2‖) := mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add le_rfl hAv)) hM
      _ ≤ M*(‖t‖+C*‖t‖) := mul_le_mul_of_nonneg_left
        (add_le_add (norm_fst_le t) (mul_le_mul_of_nonneg_left (norm_snd_le t) hC)) hM
      _ ≤ _ := by nlinarith [norm_nonneg t]
  · exact (norm_snd_le t).trans (by nlinarith [norm_nonneg t,mul_nonneg hM (by positivity : 0 ≤ 1+C)])

end NLS.ComplexAnalysis
