import NLS.ComplexAnalysis.AnalyticNonzeroConnected

/-! A finite family of scalar analytic divisors is simultaneously
nonzero densely on its connected domain once one common witness exists. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem subset_closure_finite_analytic_nonzero
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) (hc : IsConnected U) (S : Finset ι)
    (f : ι → E → ℂ) (hf : ∀ n∈S, AnalyticOnNhd ℂ (f n) U)
    (a : E) (ha : a∈U) (hne : ∀ n∈S, f n a≠0) :
    U⊆closure {x∈U | ∀ n∈S, f n x≠0} := by
  classical
  let g := fun x => ∏ n∈S, f n x
  have hg : AnalyticOnNhd ℂ g U := fun x hx =>
    S.analyticAt_fun_prod (fun n hn => hf n hn x hx)
  have hga : g a≠0 := Finset.prod_ne_zero_iff.mpr hne
  intro x hx
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨y,hy,hgy⟩ := analytic_exists_nonzero_in_open hc g hg a ha hga
    (hU.inter isOpen_ball) ⟨x,hx,mem_ball_self hε⟩ inter_subset_left
  refine ⟨y,⟨hy.1,Finset.prod_ne_zero_iff.mp hgy⟩,?_⟩
  simpa only [dist_comm] using mem_ball.mp hy.2

end NLS.ComplexAnalysis
