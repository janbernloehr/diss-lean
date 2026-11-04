import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic.FieldSimp

/-! A logarithmic differential computed from an actual exponential
germ is independent of the choice of the local additive primitive. -/
noncomputable section
open Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem logarithmic_fderiv_of_exp_germ (F θ : E → ℂ) (q : E) (c : ℂ)
    (hc : c ≠ 0) (hθ : AnalyticAt ℂ θ q)
    (he : F =ᶠ[𝓝 q] (fun p => Complex.exp (c*θ p))) :
    (c*F q)⁻¹ • fderiv ℂ F q = fderiv ℂ θ q := by
  have hd := (hθ.differentiableAt.hasFDerivAt.const_mul c).cexp
  rw [he.fderiv_eq,hd.fderiv,he.eq_of_nhds,smul_smul,smul_smul]
  have hcoef : (c*Complex.exp (c*θ q))⁻¹*(Complex.exp (c*θ q)*c)=1 := by
    field_simp [hc,Complex.exp_ne_zero]
  rw [mul_assoc,hcoef,one_smul]

end NLS.ComplexAnalysis
