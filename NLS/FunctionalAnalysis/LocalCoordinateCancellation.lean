import NLS.FunctionalAnalysis.ContinuousCoordinateCancellation

/-! Local cancellation of a real linear coordinate between continuous
functions on an open set, including every point of its zero hyperplane. -/
noncomputable section
open Set Filter Topology
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eqOn_of_continuousOn_coordinate_mul (f g : E → ℝ) (l : E →L[ℝ] ℝ) (e : E)
    (hle : l e=1) {U : Set E} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (he : ∀ z ∈ U, l z*f z=l z*g z) : EqOn f g U := by
  intro z hz
  by_cases hlz : l z=0
  · have hp : Tendsto (fun t : ℝ => z+t • e) (𝓝 0) (𝓝 z) := by
      have hc : Continuous (fun t : ℝ => z+t • e) := by fun_prop
      simpa only [zero_smul,add_zero] using hc.tendsto (0:ℝ)
    have hstay : ∀ᶠ t in 𝓝 (0:ℝ), z+t • e ∈ U := hp (hU.mem_nhds hz)
    have hnear : (fun t : ℝ => f (z+t • e)) =ᶠ[𝓝[≠] (0:ℝ)] (fun t => g (z+t • e)) := by
      filter_upwards [hstay.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht htne
      have htne' : t≠0 := htne
      have hlt : l (z+t • e)=t := by simp [hlz,hle]
      exact mul_left_cancel₀ (by simpa only [hlt] using htne') (he (z+t • e) ht)
    exact tendsto_nhds_unique_of_eventuallyEq
      (((hf.continuousAt (hU.mem_nhds hz)).tendsto.comp hp).mono_left nhdsWithin_le_nhds)
      (((hg.continuousAt (hU.mem_nhds hz)).tendsto.comp hp).mono_left nhdsWithin_le_nhds) hnear
  · exact mul_left_cancel₀ hlz (he z hz)

end NLS.FunctionalAnalysis
