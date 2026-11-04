import NLS.ComplexAnalysis.QuadraticCosinePrimitive
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Cleared variations of a cosine terminal with stationary symmetric
data. The half-gap is nonzero, while the physical terminal sheet and
the terminal sine are allowed to vanish. -/
noncomputable section
open Filter Topology Complex
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fderiv_square_root_stationary
    (d G : E → ℂ) (a h : E) (c : ℂ) (hd : DifferentiableAt ℂ d a)
    (hG : DifferentiableAt ℂ G a) (hne : d a ≠ 0)
    (hGzero : (fderiv ℂ G a) h = 0)
    (hsq : (fun b => d b^2) =ᶠ[𝓝 a] (fun b => c*G b)) :
    (fderiv ℂ d a) h = 0 := by
  have he : (fun b => d b*d b) =ᶠ[𝓝 a] (fun b => c*G b) := by
    simpa only [pow_two] using hsq
  have hleft := hd.hasFDerivAt.fun_mul hd.hasFDerivAt
  have hright := hG.hasFDerivAt.const_mul c
  have hv := congrArg (fun L : E →L[ℂ] ℂ => L h) he.fderiv_eq
  rw [hleft.fderiv,hright.fderiv] at hv
  simp only [add_apply,smul_apply,smul_eq_mul,hGzero,mul_zero] at hv
  have hz : (2*d a)*((fderiv ℂ d a) h) = 0 := by linear_combination hv
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hne)

theorem fderiv_cosine_terminal_cleared
    (μ M d ε : E → ℂ) (a h : E) (S K : ℂ)
    (hM : DifferentiableAt ℂ M a) (hd : DifferentiableAt ℂ d a)
    (hε : DifferentiableAt ℂ ε a)
    (hMzero : (fderiv ℂ M a) h = 0) (hdzero : (fderiv ℂ d a) h = 0)
    (hcos : μ =ᶠ[𝓝 a] (fun b => M b+d b*Complex.cos (ε b)))
    (hsheet : S = -I*d a*K*Complex.sin (ε a)) :
    S*((fderiv ℂ ε a) h) = I*K*((fderiv ℂ μ a) h) := by
  have hcosine := (Complex.hasDerivAt_cos (ε a)).comp_hasFDerivAt a hε.hasFDerivAt
  have hright := hM.hasFDerivAt.fun_add (hd.hasFDerivAt.fun_mul hcosine)
  simp only [Function.comp_def] at hright
  have hv := congrArg (fun L : E →L[ℂ] ℂ => L h) hcos.fderiv_eq
  rw [hright.fderiv] at hv
  simp only [add_apply,smul_apply,smul_eq_mul,hMzero,hdzero,mul_zero,zero_add] at hv
  rw [hsheet]
  linear_combination -I*K*hv

end NLS.ComplexAnalysis
