import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # The physical second amplitude derivative of an analytic action factor

The action parameter is t²/2. Its second derivative at zero is the raw
unit action direction, so no factor of two or weight is inserted.
-/
noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An actual holomorphic action factor recovers its action derivative from
the physical second derivative along the quadratic amplitude line. -/
theorem second_deriv_quadratic_action
    (H : E → ℂ) (I e : E) (hH : AnalyticAt ℂ H I) :
    deriv (deriv (fun t : ℝ => H (I+((t^2/2:ℝ):ℂ) • e))) 0 = fderiv ℂ H I e := by
  let γ : ℝ → E := fun t => I+(t^2/2) • e
  have hzero : γ 0 = I := by simp [γ]
  have hγ : AnalyticAt ℝ γ 0 := analyticAt_const.add
    (((analyticAt_id.pow 2).div_const (c := (2:ℝ))).smul analyticAt_const)
  have hdγ (t : ℝ) : HasDerivAt γ (t • e) t := by
    have h := ((hasDerivAt_id t).pow 2).div_const 2
    change HasDerivAt (fun x : ℝ => x^2/2) ((2:ℝ)*t^(2-1)*1/2) t at h
    have he : (2:ℝ)*t^(2-1)*1/2 = t := by norm_num
    rw [he] at h
    exact (h.smul_const e).const_add I

  have hr : AnalyticAt ℝ H (γ 0) := hzero.symm ▸ hH.restrictScalars (𝕜 := ℝ)
  have hd : DifferentiableAt ℝ (fun t => fderiv ℝ H (γ t) e) 0 :=
    ((hr.fderiv.comp hγ).differentiableAt).clm_apply (differentiableAt_const e)
  have heq : deriv (fun t => H (γ t)) =ᶠ[𝓝 0]
      (fun t => t • fderiv ℝ H (γ t) e) := by
    filter_upwards [hγ.continuousAt.tendsto.eventually hr.eventually_analyticAt] with t ht
    have h := ht.differentiableAt.hasFDerivAt.comp_hasDerivAt t (hdγ t)
    simpa only [Function.comp_def,map_smul] using h.deriv
  have hprod := (hasDerivAt_id (0:ℝ)).smul hd.hasDerivAt
  have hval : deriv (fun t : ℝ => t • fderiv ℝ H (γ t) e) 0 = fderiv ℝ H I e := by
    have hp := hprod.deriv
    change deriv (fun t : ℝ => t • fderiv ℝ H (γ t) e) 0 = _ at hp
    simpa only [hzero,id_eq,zero_smul,one_smul,zero_add,add_zero] using hp
  change deriv (deriv (fun t => H (γ t))) 0 = _
  rw [heq.deriv_eq,hval]
  exact congrArg (fun L : E →L[ℝ] ℂ => L e)
    (hH.differentiableAt.hasFDerivAt.restrictScalars ℝ).fderiv

end NLS.ComplexAnalysis
