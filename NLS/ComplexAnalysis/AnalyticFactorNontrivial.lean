import NLS.ComplexAnalysis.AnalyticScalarFactorUniqueness

/-! A nontrivial analytic scalar on a connected domain is nontrivial
on EVERY nonempty open subset of that domain, including disconnected subsets. -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analytic_exists_nonzero_on_nonempty_open {D U : Set E}
    (hD : IsPreconnected D) (hU : IsOpen U) (hUD : U ⊆ D) (hUne : U.Nonempty)
    (f : E → ℂ) (hf : AnalyticOnNhd ℂ f D) (hne : ∃ a ∈ D, f a ≠ 0) :
    ∃ a ∈ U, f a ≠ 0 := by
  by_contra h
  have hzero : ∀ a ∈ U, f a=0 := by simpa only [not_exists,not_and,not_not] using h
  have he := analytic_eqOn_of_mul_eq_mul_on_open hD hU hUD f (fun _ => 1) (fun _ => 0)
    hf analyticOnNhd_const analyticOnNhd_const hne (by intro a ha; rw [hzero a ha]; simp)
  obtain ⟨a,ha⟩ := hUne
  have hz : (1:ℂ)=0 := he ha
  norm_num at hz

end NLS.ComplexAnalysis
