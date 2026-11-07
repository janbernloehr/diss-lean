import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Analytic.Constructions

/-! FULL real Banach analyticity and derivatives of complex-valued bounded
bilinear quadratic forms composed with a genuine Banach-analytic map.
No complex-holomorphic norm-square assertion is made. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


/-- Pull back a bounded real bilinear form along the SAME bounded linear map. -/
def realBilinearPullback (B : F →L[ℝ] F →L[ℝ] ℂ) (A : E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] ℂ :=
  B.bilinearComp A A

theorem analyticAt_real_bilinear_quadratic_comp (B : F →L[ℝ] F →L[ℝ] ℂ) (c : ℂ)
    (f : E → F) (u : E) (hf : AnalyticAt ℝ f u) :
    AnalyticAt ℝ (fun x => c*B (f x) (f x)) u :=
  analyticAt_const.mul ((B.analyticAt_bilinear _).comp₂ hf hf)

theorem fderiv_real_bilinear_quadratic_comp_apply (B : F →L[ℝ] F →L[ℝ] ℂ) (c : ℂ)
    (f : E → F) (u h : E) (hf : DifferentiableAt ℝ f u) :
    (fderiv ℝ (fun x => c*B (f x) (f x)) u) h=
      c*(B (f u) ((fderiv ℝ f u) h)+B ((fderiv ℝ f u) h) (f u)) := by
  have hd := ((B.hasFDerivAt_of_bilinear hf.hasFDerivAt hf.hasFDerivAt).const_mul c).fderiv
  change fderiv ℝ (fun x => c*B (f x) (f x)) u= _ at hd
  rw [hd]
  rfl


/-- A product of two bounded linear coordinate tests after a differentiable
Banach map, with the full real derivative retained. -/
theorem fderiv_real_linear_product_comp_apply (L M : F →L[ℝ] ℂ)
    (f : E → F) (u h : E) (hf : DifferentiableAt ℝ f u) :
    (fderiv ℝ (fun x => L (f x)*M (f x)) u) h=
      L ((fderiv ℝ f u) h)*M (f u)+L (f u)*M ((fderiv ℝ f u) h) := by
  have hl := L.hasFDerivAt.comp u hf.hasFDerivAt
  have hm := M.hasFDerivAt.comp u hf.hasFDerivAt
  have hd := (hl.mul hm).fderiv
  change fderiv ℝ (fun x => L (f x)*M (f x)) u= _ at hd
  rw [hd]
  change L (f u)*M ((fderiv ℝ f u) h)+M (f u)*L ((fderiv ℝ f u) h)= _
  ring

end NLS.FunctionalAnalysis
