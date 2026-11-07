import NLS.ComplexAnalysis.ZeroFactorCotangent
import Mathlib.Tactic.FieldSimp

/-! Full scalar cotangents from an exact product and a phase ratio.
The logarithmic ratio differential needs no additive phase choice
and no chosen square root of the product. -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fderiv_from_product_phase_ratio (f g : E → ℂ) (q : E)
    (hf : DifferentiableAt ℂ f q) (hg : DifferentiableAt ℂ g q)
    (hfnz : f q ≠ 0) (hgnz : g q ≠ 0) :
    fderiv ℂ f q = f q • ((2*(f q*g q))⁻¹ • fderiv ℂ (fun p => f p*g p) q -
      I • ((2*I*(g q/f q))⁻¹ • fderiv ℂ (fun p => g p/f p) q)) ∧
    fderiv ℂ g q = g q • ((2*(f q*g q))⁻¹ • fderiv ℂ (fun p => f p*g p) q +
      I • ((2*I*(g q/f q))⁻¹ • fderiv ℂ (fun p => g p/f p) q)) := by
  have hP := hf.hasFDerivAt.fun_mul hg.hasFDerivAt
  have hfi := (hasDerivAt_inv hfnz).comp_hasFDerivAt q hf.hasFDerivAt
  have hR := hg.hasFDerivAt.fun_mul hfi
  change HasFDerivAt (fun p => g p/f p) _ q at hR
  rw [hP.fderiv,hR.fderiv]
  constructor <;> ext h <;>
    simp only [add_apply,sub_apply,smul_apply,smul_eq_mul,Function.comp_def] <;>
    field_simp [hfnz,hgnz] <;> ring

end NLS.ComplexAnalysis
