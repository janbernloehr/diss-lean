import NLS.ComplexAnalysis.BanachTaylorBounds

/-! # Uniform scalar cotangent bounds from one local analytic family bound -/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- One local scalar bound before the family index bounds all derivatives
at the center in operator norm. Only coordinatewise analyticity is needed. -/
theorem exists_uniform_fderiv_bound_of_local_bound
    (f : ι → E → ℂ) (U : Set E) (hU : IsOpen U) (h0 : (0 : E) ∈ U)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (M : ℝ) (hb : ∀ᶠ a in 𝓝 (0 : E), ∀ i, ‖f i a‖ ≤ M) :
    ∃ K : ℝ, ∀ i, ‖fderiv ℂ (f i) 0‖ ≤ K := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds h0) hb)
  refine ⟨4*M/r,fun i => ?_⟩
  have he : r/2+r/2=r := by ring
  have hd := norm_fderiv_le_of_ball_bound (f i) 0 0 (r/2) (r/2) M (by positivity)
    (by rw [he]; exact (hf i).differentiableOn.mono (fun a ha => (hball ha).1))
    (by rw [he]; exact fun a ha => (hball ha).2 i) (mem_ball_self (by positivity))
  apply hd.trans_eq
  ring

end NLS.ComplexAnalysis
