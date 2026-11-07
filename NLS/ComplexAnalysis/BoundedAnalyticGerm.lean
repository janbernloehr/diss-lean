import NLS.ComplexAnalysis.AnalyticDomainPullback

noncomputable section
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis

theorem exists_bounded_analytic_germ
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (V : Set E) (hV : IsOpen V) (q : E) (hq : q∈V)
    (f : E → F) (hfa : AnalyticOnNhd 𝕜 f V) :
    ∃ U : Set E,IsOpen U ∧ q∈U ∧ U⊆V ∧ ∃ C : ℝ,
      0≤C ∧ AnalyticOnNhd 𝕜 f U ∧ ∀ p∈U,‖f p‖≤C := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hV.mem_nhds hq)
    ((hfa q hq).continuousAt (ball_mem_nhds (f q) (by norm_num : (0:ℝ)<1))))
  refine ⟨ball q r,isOpen_ball,mem_ball_self hr,(fun p hp => (hball hp).1),‖f q‖+1,
    by positivity,hfa.mono (fun p hp => (hball hp).1),?_⟩
  intro p hp
  have ht : ‖f p-f q‖<1 := by
    simpa only [mem_preimage,mem_ball,dist_eq_norm] using (hball hp).2
  exact (norm_le_norm_sub_add (f p) (f q)).trans (by linarith)

end NLS.ComplexAnalysis
