import NLS.ComplexAnalysis.AnalyticGermCancellation

/-! # A scalar analytic square fixes the coordinate up to one constant sign -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.ComplexAnalysis

theorem analytic_germ_eq_or_eq_neg_of_sq_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℂ} {a : E} (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
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
    have hz := analytic_germ_cancel (hf.sub hg) (hf.add hg) hp hn
    exact hz.mono (fun _ hx => eq_neg_of_add_eq_zero_left hx)

end NLS.ComplexAnalysis
