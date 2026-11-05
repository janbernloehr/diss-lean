import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
set_option autoImplicit false
open Complex
open scoped Classical

namespace NLS.Poisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The literal bracket determined by a fixed bounded Hamiltonian operator. -/
def constantOperatorBracket (J : (E →L[ℂ] ℂ) →L[ℂ] E) (F G : E → ℂ) (q : E) : ℂ :=
  (fderiv ℂ F q) (J (fderiv ℂ G q))

/-- The actual constant-operator bracket derivative is the difference of
its two Hessian terms, with no Jacobi or canonicality premise. -/
theorem fderiv_constantOperatorBracket_apply
    (J : (E →L[ℂ] ℂ) →L[ℂ] E)
    (hJ : ∀ L M : E →L[ℂ] ℂ, L (J M)= -M (J L))
    (F G : E → ℂ) (q v : E) (hF : AnalyticAt ℂ F q) (hG : AnalyticAt ℂ G q) :
    (fderiv ℂ (constantOperatorBracket J F G) q) v=
      (fderiv ℂ (fderiv ℂ F) q) v (J (fderiv ℂ G q))-
        (fderiv ℂ (fderiv ℂ G) q) v (J (fderiv ℂ F q)) := by
  have hd := hF.fderiv.differentiableAt.hasFDerivAt.clm_apply
    (J.hasFDerivAt.comp q hG.fderiv.differentiableAt.hasFDerivAt)
  change HasFDerivAt (constantOperatorBracket J F G) _ q at hd
  rw [hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,Function.comp_def]
  rw [hJ]
  ring

/-- Hessian symmetry proves Jacobi for every actual bounded constant skew
Hamiltonian operator on a complex normed source space. -/
theorem constantOperatorBracket_jacobi
    (J : (E →L[ℂ] ℂ) →L[ℂ] E)
    (hJ : ∀ L M : E →L[ℂ] ℂ, L (J M)= -M (J L))
    (F G H : E → ℂ) (q : E)
    (hF : AnalyticAt ℂ F q) (hG : AnalyticAt ℂ G q) (hH : AnalyticAt ℂ H q) :
    constantOperatorBracket J (constantOperatorBracket J F G) H q+
      constantOperatorBracket J (constantOperatorBracket J G H) F q+
      constantOperatorBracket J (constantOperatorBracket J H F) G q=0 := by
  change (fderiv ℂ (constantOperatorBracket J F G) q) (J (fderiv ℂ H q))+
    (fderiv ℂ (constantOperatorBracket J G H) q) (J (fderiv ℂ F q))+
    (fderiv ℂ (constantOperatorBracket J H F) q) (J (fderiv ℂ G q))=0
  rw [fderiv_constantOperatorBracket_apply J hJ F G q _ hF hG,
    fderiv_constantOperatorBracket_apply J hJ G H q _ hG hH,
    fderiv_constantOperatorBracket_apply J hJ H F q _ hH hF]
  have hsF := (hF.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num)
  have hsG := (hG.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num)
  have hsH := (hH.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num)
  rw [hsF.eq (J (fderiv ℂ H q)) (J (fderiv ℂ G q)),
    hsG.eq (J (fderiv ℂ H q)) (J (fderiv ℂ F q)),
    hsH.eq (J (fderiv ℂ F q)) (J (fderiv ℂ G q))]
  ring

/-- The infinitesimal transport identity for the actual constant-operator
bracket, expressed in derivatives of its two mixed brackets. -/
theorem constantOperatorBracket_hamiltonian_derivative
    (J : (E →L[ℂ] ℂ) →L[ℂ] E)
    (hJ : ∀ L M : E →L[ℂ] ℂ, L (J M)= -M (J L))
    (F G H : E → ℂ) (q : E)
    (hF : AnalyticAt ℂ F q) (hG : AnalyticAt ℂ G q) (hH : AnalyticAt ℂ H q) :
    (fderiv ℂ (constantOperatorBracket J F G) q) (J (fderiv ℂ H q))=
      (fderiv ℂ (constantOperatorBracket J F H) q) (J (fderiv ℂ G q))-
        (fderiv ℂ (constantOperatorBracket J G H) q) (J (fderiv ℂ F q)) := by
  rw [fderiv_constantOperatorBracket_apply J hJ F G q _ hF hG,
    fderiv_constantOperatorBracket_apply J hJ F H q _ hF hH,
    fderiv_constantOperatorBracket_apply J hJ G H q _ hG hH]
  have hsF := (hF.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num)
  have hsG := (hG.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num)
  have hsH := (hH.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num)
  rw [hsF.eq (J (fderiv ℂ H q)) (J (fderiv ℂ G q)),
    hsG.eq (J (fderiv ℂ H q)) (J (fderiv ℂ F q)),
    hsH.eq (J (fderiv ℂ G q)) (J (fderiv ℂ F q))]
  ring

end NLS.Poisson
