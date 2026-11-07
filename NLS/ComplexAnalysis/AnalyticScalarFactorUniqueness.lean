import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Topology

/-! # Cancellation of a nontrivial analytic scalar factor on an open subset

The ambient connected domain, rather than each open subset, carries the
nontriviality hypothesis. The open subset may be disconnected. No
assumption that the factor is nonzero at the comparison point is needed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis

theorem analytic_eqOn_of_mul_eq_mul_on_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {D U : Set E} (hD : IsPreconnected D) (hU : IsOpen U) (hUD : U ⊆ D)
    (f g h : E → ℂ) (hf : AnalyticOnNhd ℂ f D)
    (hg : AnalyticOnNhd ℂ g U) (hh : AnalyticOnNhd ℂ h U)
    (hne : ∃ a ∈ D, f a ≠ 0) (he : ∀ a ∈ U, f a*g a = f a*h a) : EqOn g h U := by
  intro x hx
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hnonzero : ∃ w ∈ ball x r, f w ≠ 0 := by
    by_contra hn
    push Not at hn
    have hz : f =ᶠ[𝓝 x] 0 := by
      filter_upwards [ball_mem_nhds x hr] with a ha
      exact hn a ha
    obtain ⟨a,ha,hfa⟩ := hne
    exact hfa (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hD (hUD hx) hz ha)
  obtain ⟨w,hw,hfw⟩ := hnonzero
  have hloc : g =ᶠ[𝓝 w] h := by
    filter_upwards [isOpen_ball.mem_nhds hw,(hf w (hUD (hball hw))).continuousAt.eventually_ne hfw] with a ha hfa
    exact mul_left_cancel₀ hfa (he a (hball ha))
  exact ((hg.mono hball).eqOn_of_preconnected_of_eventuallyEq (hh.mono hball)
    (convex_ball x r).isPreconnected hw hloc) (mem_ball_self hr)

end NLS.ComplexAnalysis
