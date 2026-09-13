import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Local logarithmic derivatives and analytic zero orders

A finite-order analytic germ factors as a power of the centered coordinate
times a nonvanishing analytic germ. Its logarithmic derivative therefore has
one simple pole, whose coefficient is exactly the natural analytic order.
-/

noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis

/-- The logarithmic derivative of a nonvanishing analytic germ is analytic. -/
theorem analyticAt_logDeriv {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c) (hc : f c ≠ 0) :
    AnalyticAt ℂ (logDeriv f) c := hf.deriv.div hf hc

/-- At a finite-order zero, subtracting the analytic order divided by the centered coordinate
leaves an analytic germ. The equality is on a punctured neighborhood. -/
theorem exists_analytic_logDeriv_remainder {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hfinite : analyticOrderAt f c ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g c ∧
      logDeriv f =ᶠ[𝓝[≠] c] (fun z => (analyticOrderNatAt f c : ℂ)/(z-c) + g z) := by
  obtain ⟨u, hu, hu0, hfactor⟩ := hf.analyticOrderAt_ne_top.mp hfinite
  simp only [smul_eq_mul] at hfactor
  refine ⟨logDeriv u, analyticAt_logDeriv hu hu0, ?_⟩
  have he := logDeriv_congr_nhds hfactor
  have hune := hu.continuousAt.eventually_ne hu0
  filter_upwards [he.filter_mono nhdsWithin_le_nhds,
    hu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hune.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzu hzne hzc
  have hzc' : z-c ≠ 0 := sub_ne_zero.mpr hzc
  rw [hz, logDeriv_mul (f := fun z : ℂ => (z-c)^analyticOrderNatAt f c) (g := u) z (pow_ne_zero _ hzc') hzne (by fun_prop) hzu.differentiableAt,
    logDeriv_fun_pow (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z-c) z)]
  simp [logDeriv_apply, div_eq_mul_inv]

end NLS.ComplexAnalysis
