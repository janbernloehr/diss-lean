import NLS.Articles.KdVPseudomeasures.SourceLemma57

/-! Explicit locally uniform bounds and analytic mode frequencies
for the unweighted lp-valued remainder in Lemma 5.7. -/
noncomputable section
open Set Filter Topology NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem lemma57_local_norm_bound
    {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    (H : E → B) (U : Set E) (hU : IsOpen U) (hH : AnalyticOnNhd ℂ H U)
    (z : E) (hz : z ∈ U) :
    ∃ V : Set E, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ y ∈ V, ‖H y‖ ≤ R := by
  have hn : ∀ᶠ y in 𝓝 z, ‖H y‖ < ‖H z‖+1 :=
    (hH z hz).continuousAt.norm.tendsto.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨V,hVsub,hV,hzV⟩ := _root_.mem_nhds_iff.mp (hn.and (hU.mem_nhds hz))
  exact ⟨V,hV,hzV,(fun _ hy => (hVsub hy).2),‖H z‖+1,by positivity,
    fun y hy => le_of_lt (hVsub hy).1⟩

theorem lemma57_mode_analytic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → NLS.Coeff ⊤) (U : Set E) (hF : AnalyticOnNhd ℂ F U) (n : ℕ+) :
    AnalyticOnNhd ℂ (fun z => (2*(Real.pi:ℂ)*(n:ℤ))^3+F z (n:ℤ)) U := by
  let L : NLS.Coeff ⊤ →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ (n:ℤ)
  intro z hz
  have h : AnalyticAt ℂ (fun z => F z (n:ℤ)) z :=
    (L.analyticAt (F z)).comp (hF z hz)
  exact analyticAt_const.add h

end NLS.Articles.KdVPseudomeasures
