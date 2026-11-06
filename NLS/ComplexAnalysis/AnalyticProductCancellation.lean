import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic

/-! Analytic continuation cancels a scalar multiplier that is nonzero
at one actual source. No pointwise nonvanishing on the whole domain
or division on its zero set is required. -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem analytic_eqOn_of_mul_sub_eq_zero
    (U : Set A) (hU : IsOpen U) (hconn : IsPreconnected U)
    (f g h : A → ℂ) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hh : AnalyticOnNhd ℂ h U) (a : A) (ha : a ∈ U) (hne : h a ≠ 0)
    (hprod : ∀ p ∈ U, h p*(f p-g p)=0) : EqOn f g U := by
  have hnonzero : ∀ᶠ p in 𝓝 a, h p ≠ 0 := (hh a ha).continuousAt.eventually_ne hne
  have he : f =ᶠ[𝓝 a] g := by
    filter_upwards [hU.mem_nhds ha,hnonzero] with p hp hn
    exact sub_eq_zero.mp ((mul_eq_zero.mp (hprod p hp)).resolve_left hn)
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn ha he

end NLS.ComplexAnalysis

/-! # Cancellation of a nonzero continuous factor in an analytic identity -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PreconnectedSpace E]

theorem eq_zero_of_analytic_mul_eq_zero (f g : E → ℂ)
    (hg : AnalyticOnNhd ℝ g univ) (hfg : ∀ x, f x*g x = 0)
    (b : E) (hf : ContinuousAt f b) (hb : f b ≠ 0) : ∀ x, g x = 0 := by
  have hnear : g =ᶠ[𝓝 b] fun _ => 0 := by
    filter_upwards [hf.eventually_ne hb] with x hx
    exact (mul_eq_zero.mp (hfg x)).resolve_left hx
  have he := hg.eq_of_eventuallyEq analyticOnNhd_const hnear
  exact fun x => congrFun he x

end NLS.ComplexAnalysis
