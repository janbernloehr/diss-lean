import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Continuous Hadamard division by a real linear coordinate. Integrating
the transverse derivative fills the entire zero hyperplane without division. -/
noncomputable section
open MeasureTheory intervalIntegral
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analyticAt_fderiv_apply_const (f : E → ℝ) (e x : E) (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (fderiv ℝ f y) e) x :=
  ((ContinuousLinearMap.apply ℝ ℝ e).analyticAt _).comp hf.fderiv

theorem continuous_fderiv_of_analytic (f : E → ℝ) (hf : ∀ x, AnalyticAt ℝ f x) :
    Continuous (fderiv ℝ f) :=
  continuous_iff_continuousAt.mpr (fun x => (hf x).fderiv.continuousAt)

def hyperplaneSlope (f : E → ℝ) (l : E →L[ℝ] ℝ) (e x : E) : ℝ :=
  ∫ t in (0:ℝ)..1, (fderiv ℝ f (x-l x • e+t • (l x • e))) e

theorem continuous_hyperplaneSlope (f : E → ℝ) (l : E →L[ℝ] ℝ) (e : E)
    (hf : Continuous (fderiv ℝ f)) : Continuous (hyperplaneSlope f l e) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := 0) (b₀ := 1)
  have hpath : Continuous (fun p : E × ℝ => p.1-l p.1 • e+p.2 • (l p.1 • e)) := by fun_prop
  exact (hf.comp hpath).clm_apply continuous_const

theorem mul_hyperplaneSlope (f : E → ℝ) (l : E →L[ℝ] ℝ) (e : E)
    (hle : l e=1) (hf : Differentiable ℝ f) (hc : Continuous (fderiv ℝ f))
    (hzero : ∀ x, l x=0 → f x=0) (x : E) :
    l x*hyperplaneSlope f l e x=f x := by
  let b := x-l x • e
  have hb : l b=0 := by simp [b,hle]
  have hbzero : f b=0 := hzero b hb
  have hline (t : ℝ) : HasDerivAt (fun r : ℝ => b+r • (l x • e)) (l x • e) t := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id t).smul_const (l x • e)).const_add b
  have hd (t : ℝ) : HasDerivAt (fun r : ℝ => f (b+r • (l x • e)))
      (l x*((fderiv ℝ f (b+t • (l x • e))) e)) t := by
    simpa only [Function.comp_def,map_smul,smul_eq_mul] using
      (hf (b+t • (l x • e))).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hi : IntervalIntegrable
      (fun t : ℝ => l x*((fderiv ℝ f (b+t • (l x • e))) e)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((hc.comp (by fun_prop)).clm_apply continuous_const)
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_const_mul] at ht
  have h1 : b+(1:ℝ) • (l x • e)=x := by simp [b]
  simpa only [hyperplaneSlope,b,h1,zero_smul,add_zero,hbzero,sub_zero] using ht

end NLS.FunctionalAnalysis
