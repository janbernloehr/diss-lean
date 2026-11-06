import NLS.ComplexAnalysis.AnalyticGermSign

/-! # Constant signs for complex-valued real analytic maps

The domain is a real Banach space. A scalar may vanish at the base:
nontriviality of its analytic germ suffices for cancellation.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis

theorem real_analytic_germ_cancel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℂ} {a : E} (hf : AnalyticAt ℝ f a) (hg : AnalyticAt ℝ g a)
    (hfg : ∀ᶠ x in 𝓝 a, f x*g x=0)
    (hfn : ¬ ∀ᶠ x in 𝓝 a, f x=0) : ∀ᶠ x in 𝓝 a, g x=0 := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and hfg)
  have hfa : AnalyticOnNhd ℝ f (ball a r) := fun x hx => (hball hx).1.1
  have hga : AnalyticOnNhd ℝ g (ball a r) := fun x hx => (hball hx).1.2
  have hex : ∃ x ∈ ball a r, f x≠0 := by
    by_contra! hn
    exact hfn (mem_of_superset (ball_mem_nhds a hr) hn)
  obtain ⟨b,hb,hfb⟩ := hex
  have hbzero : ∀ᶠ x in 𝓝 b, g x=0 := by
    filter_upwards [isOpen_ball.mem_nhds hb,(hfa b hb).continuousAt.eventually_ne hfb] with x hx hfx
    exact (mul_eq_zero.mp (hball hx).2).resolve_left hfx
  have hz := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_ball hb hbzero
  exact mem_of_superset (ball_mem_nhds a hr) hz

theorem real_analytic_germ_eq_or_eq_neg_of_sq_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℂ} {a : E} (hf : AnalyticAt ℝ f a) (hg : AnalyticAt ℝ g a)
    (hsq : ∀ᶠ x in 𝓝 a, (f x)^2=(g x)^2) :
    f =ᶠ[𝓝 a] g ∨ f =ᶠ[𝓝 a] (fun x => -g x) := by
  by_cases he : f =ᶠ[𝓝 a] g
  · exact Or.inl he
  · apply Or.inr
    have hn : ¬ ∀ᶠ x in 𝓝 a, f x-g x=0 := by
      intro hh
      exact he (hh.mono (fun _ hx => sub_eq_zero.mp hx))
    have hp : ∀ᶠ x in 𝓝 a, (f x-g x)*(f x+g x)=0 := by
      filter_upwards [hsq] with x hx
      linear_combination hx
    have hz := real_analytic_germ_cancel (hf.sub hg) (hf.add hg) hp hn
    exact hz.mono (fun _ hx => eq_neg_of_add_eq_zero_left hx)

theorem real_analytic_eqOn_or_neg_of_sq_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hU : IsOpen U) (hconn : IsPreconnected U)
    (a : E) (ha : a ∈ U) (f g : E → ℂ)
    (hf : AnalyticOnNhd ℝ f U) (hg : AnalyticOnNhd ℝ g U)
    (hsq : ∀ x ∈ U, (f x)^2=(g x)^2) :
    EqOn f g U ∨ EqOn f (fun x => -g x) U := by
  have hnear : ∀ᶠ x in 𝓝 a, (f x)^2=(g x)^2 := by
    filter_upwards [hU.mem_nhds ha] with x hx
    exact hsq x hx
  rcases real_analytic_germ_eq_or_eq_neg_of_sq_eq (hf a ha) (hg a ha) hnear with h | h
  · exact Or.inl (hf.eqOn_of_preconnected_of_eventuallyEq hg hconn ha h)
  · exact Or.inr (hf.eqOn_of_preconnected_of_eventuallyEq (fun x hx => (hg x hx).neg) hconn ha h)

end NLS.ComplexAnalysis
