import NLS.KdV.HillIndexedFlowSpeed
import NLS.FunctionalAnalysis.RelativeUniformLimit

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Every original mean-zero indexed spectral trajectory has strong limits
in the actual complete real source space at both finite endpoints of
its interval of definition. No compactness of a source ball is assumed. -/
theorem exists_hillIndexedIntegralCurve_endpoint_limits
    (k : ℕ) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (a b : ℝ)
    (hγ : ∀ t∈Ioo a b, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (u : ℝ) (hu : u∈Ioo a b) (hmean : (γ u).val.val 0=0) :
    ∃ qLeft qRight : hillRealSourceSubmodule,
      Tendsto γ (𝓝[Ioo a b] a) (𝓝 qLeft) ∧ Tendsto γ (𝓝[Ioo a b] b) (𝓝 qRight) := by
  obtain ⟨A,hA,hbound⟩ := exists_hillIndexedIntegralCurve_uniform_speed_bound k hk γ a b hγ u hu hmean
  have hLip : LipschitzOnWith (⟨A,hA.le⟩ : NNReal) γ (Ioo a b) :=
    Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun t ht => (hγ t ht).differentiableAt)
      (fun t ht => by change ‖deriv γ t‖≤A;exact hbound t ht) (convex_Ioo a b)
  have hab : a<b := hu.1.trans hu.2
  have ha : a∈closure (Ioo a b) := by rw [closure_Ioo hab.ne];exact ⟨le_rfl,hab.le⟩
  have hb : b∈closure (Ioo a b) := by rw [closure_Ioo hab.ne];exact ⟨hab.le,le_rfl⟩
  obtain ⟨qLeft,hLeft⟩ := exists_tendsto_nhdsWithin_of_uniformContinuousOn γ (Ioo a b) hLip.uniformContinuousOn a ha
  obtain ⟨qRight,hRight⟩ := exists_tendsto_nhdsWithin_of_uniformContinuousOn γ (Ioo a b) hLip.uniformContinuousOn b hb
  exact ⟨qLeft,qRight,hLeft,hRight⟩

end NLS.KdV
