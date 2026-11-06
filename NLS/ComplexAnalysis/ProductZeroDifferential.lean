import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
set_option autoImplicit false
namespace NLS.ComplexAnalysis

/-- If one scalar factor vanishes, its partner contributes only its base
value to the product differential. -/
theorem fderiv_mul_of_left_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : E → ℂ) (x : E) (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (hzero : f x = 0) :
    fderiv ℂ (fun p => f p*g p) x = g x • fderiv ℂ f x := by
  have hP := hf.differentiableAt.hasFDerivAt.mul hg.differentiableAt.hasFDerivAt
  have hd : HasFDerivAt (fun p => f p*g p) (g x • fderiv ℂ f x) x := by
    convert! hP using 1
    ext v
    simp [hzero]
  exact hd.fderiv

/-- A multiplier equal to one does not change the differential of a
vanishing analytic scalar factor. -/
theorem fderiv_mul_of_left_zero_right_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : E → ℂ) (x : E) (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (hzero : f x = 0) (hone : g x = 1) :
    fderiv ℂ (fun p => f p*g p) x = fderiv ℂ f x := by
  rw [fderiv_mul_of_left_zero f g x hf hg hzero,hone,one_smul]

end NLS.ComplexAnalysis
