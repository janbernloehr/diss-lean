import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected

/-! # Cancellation by a nontrivial scalar analytic germ

The multiplier may vanish at the base point. Nontriviality of its germ,
rather than division at that point, suffices for cancellation.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis

theorem analytic_germ_cancel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℂ} {a : E} (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hfg : ∀ᶠ x in 𝓝 a, f x*g x=0)
    (hfn : ¬ ∀ᶠ x in 𝓝 a, f x=0) : ∀ᶠ x in 𝓝 a, g x=0 := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and hfg)
  have hfa : AnalyticOnNhd ℂ f (ball a r) := fun x hx => (hball hx).1.1
  have hga : AnalyticOnNhd ℂ g (ball a r) := fun x hx => (hball hx).1.2
  have hex : ∃ x ∈ ball a r, f x≠0 := by
    by_contra! hn
    exact hfn (mem_of_superset (ball_mem_nhds a hr) hn)
  obtain ⟨b,hb,hfb⟩ := hex
  have hbzero : ∀ᶠ x in 𝓝 b, g x=0 := by
    filter_upwards [isOpen_ball.mem_nhds hb,(hfa b hb).continuousAt.eventually_ne hfb] with x hx hfx
    exact (mul_eq_zero.mp (hball hx).2).resolve_left hfx
  have hz := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_ball hb hbzero
  exact mem_of_superset (ball_mem_nhds a hr) hz

theorem analytic_germ_cancel_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g h : E → ℂ} {a : E}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) (hh : AnalyticAt ℂ h a)
    (he : ∀ᶠ x in 𝓝 a, f x*g x=f x*h x)
    (hfn : ¬ ∀ᶠ x in 𝓝 a, f x=0) : g =ᶠ[𝓝 a] h := by
  have hz := analytic_germ_cancel hf (hg.sub hh) (he.mono (fun x hx => by
    change f x*(g x-h x)=0
    rw [mul_sub,hx,sub_self])) hfn
  exact hz.mono (fun _ hx => sub_eq_zero.mp hx)

end NLS.ComplexAnalysis
