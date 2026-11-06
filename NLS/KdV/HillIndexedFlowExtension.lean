import NLS.KdV.HillIndexedFlowEndpointLimits
import NLS.FunctionalAnalysis.IntegralCurveJoin

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- An actual mean-zero indexed Hill trajectory extends through every finite
right endpoint, preserving the original trajectory on its entire old interval. -/
theorem exists_hillIndexedIntegralCurve_extend_right
    (k : ℕ) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (a b : ℝ)
    (hγ : ∀ t∈Ioo a b, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (u : ℝ) (hu : u∈Ioo a b) (hmean : (γ u).val.val 0=0) :
    ∃ ε : ℝ, 0<ε ∧ ∃ Γ : ℝ → hillRealSourceSubmodule,
      EqOn Γ γ (Ioo a b) ∧
      ∀ t∈Ioo a (b+ε), HasDerivAt Γ (hillRealIndexedDiscriminantField k hk (Γ t)) t := by
  obtain ⟨_,qRight,_,hlimit⟩ := exists_hillIndexedIntegralCurve_endpoint_limits k hk γ a b hγ u hu hmean
  obtain ⟨η,hη0,ε,hε,hη⟩ := (contDiff_hillRealIndexedDiscriminantField k hk).contDiffAt
    (x := qRight) |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ b
  have hb : b∈Ioo (b-ε) (b+ε) := by constructor <;> linarith
  have hηlim : Tendsto η (𝓝[Ioo b (b+ε)] b) (𝓝 qRight) := by
    have hh := (hη b hb).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioo b (b+ε)))
    simpa only [hη0] using hh
  let Γ := joinIntegralCurve b qRight γ η
  refine ⟨ε,hε,Γ,fun t ht => joinIntegralCurve_of_lt b qRight γ η ht.2,?_⟩
  exact hasDerivAt_joinIntegralCurve (hillRealIndexedDiscriminantField k hk) γ η qRight a b (b+ε)
    (hu.1.trans hu.2) (by linarith) hγ
    (fun t ht => hη t ⟨by linarith [ht.1],ht.2⟩) hlimit hηlim
    (contDiff_hillRealIndexedDiscriminantField k hk).continuous.continuousAt

/-- An actual mean-zero indexed Hill trajectory likewise extends through
every finite left endpoint in the original complete real source space. -/
theorem exists_hillIndexedIntegralCurve_extend_left
    (k : ℕ) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (a b : ℝ)
    (hγ : ∀ t∈Ioo a b, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (u : ℝ) (hu : u∈Ioo a b) (hmean : (γ u).val.val 0=0) :
    ∃ ε : ℝ, 0<ε ∧ ∃ Γ : ℝ → hillRealSourceSubmodule,
      EqOn Γ γ (Ioo a b) ∧
      ∀ t∈Ioo (a-ε) b, HasDerivAt Γ (hillRealIndexedDiscriminantField k hk (Γ t)) t := by
  obtain ⟨qLeft,_,hlimit,_⟩ := exists_hillIndexedIntegralCurve_endpoint_limits k hk γ a b hγ u hu hmean
  obtain ⟨η,hη0,ε,hε,hη⟩ := (contDiff_hillRealIndexedDiscriminantField k hk).contDiffAt
    (x := qLeft) |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ a
  have ha : a∈Ioo (a-ε) (a+ε) := by constructor <;> linarith
  have hηlim : Tendsto η (𝓝[Ioo (a-ε) a] a) (𝓝 qLeft) := by
    have hh := (hη a ha).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioo (a-ε) a))
    simpa only [hη0] using hh
  let Γ := joinIntegralCurve a qLeft η γ
  refine ⟨ε,hε,Γ,fun t ht => joinIntegralCurve_of_gt a qLeft η γ ht.1,?_⟩
  exact hasDerivAt_joinIntegralCurve (hillRealIndexedDiscriminantField k hk) η γ qLeft (a-ε) a b
    (by linarith) (hu.1.trans hu.2) (fun t ht => hη t ⟨ht.1,by linarith [ht.2]⟩) hγ
    hηlim hlimit (contDiff_hillRealIndexedDiscriminantField k hk).continuous.continuousAt

end NLS.KdV
