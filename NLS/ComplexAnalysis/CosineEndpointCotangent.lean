import NLS.ComplexAnalysis.QuadraticCosinePrimitive
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! At a zero root terminal of a nonzero cosine half-gap, the full
angle cotangent is a scalar multiple of the full root cotangent.
No stationarity assumption is placed on the moving half-gap. -/
noncomputable section
open Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_fderiv_angle_eq_root_smul_at_zero_terminal
    (d θ R : E → ℂ) (q : E) (hd : DifferentiableAt ℂ d q)
    (hθ : DifferentiableAt ℂ θ q) (hdne : d q ≠ 0) (hRzero : R q=0)
    (hroot : R =ᶠ[𝓝 q] (fun p => -I*d p*Complex.sin (θ p))) :
    ∃ a : ℂ, fderiv ℂ θ q=a • fderiv ℂ R q := by
  have hs : Complex.sin (θ q)=0 := by
    have he := hroot.eq_of_nhds
    rw [hRzero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hdne)
  have hc : Complex.cos (θ q) ≠ 0 := by
    intro he
    have ht := Complex.sin_sq_add_cos_sq (θ q)
    rw [hs,he] at ht
    norm_num at ht
  let c := -I*d q*Complex.cos (θ q)
  have hcn : c ≠ 0 := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hdne) hc
  have hsin := (Complex.hasDerivAt_sin (θ q)).comp_hasFDerivAt q hθ.hasFDerivAt
  have hprod := (hd.hasFDerivAt.const_mul (-I)).fun_mul hsin
  simp only [Function.comp_def] at hprod
  have he : fderiv ℂ R q=c • fderiv ℂ θ q := by
    rw [hroot.fderiv_eq,hprod.fderiv]
    ext v
    simp only [c,add_apply,smul_apply,smul_eq_mul,hs,zero_mul,add_zero,mul_assoc]
  refine ⟨c⁻¹,?_⟩
  rw [he,smul_smul,inv_mul_cancel₀ hcn,one_smul]

end NLS.ComplexAnalysis
