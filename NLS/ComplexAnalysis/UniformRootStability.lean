import NLS.ComplexAnalysis.Rouche
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Root stability under locally uniform convergence

Compact sets without zeros stay without zeros. Rouché fixes the zero count
inside a circle, and a unique root in a compact set attracts every nearby
selected root. These statements allow arbitrary parameter filters.
-/

noncomputable section
open Filter Topology Metric
namespace NLS.ComplexAnalysis

/-- A locally uniform limit that is nonzero on a compact set keeps nearby functions nonzero there. -/
theorem eventually_ne_zero_on_compact {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {g : ℂ → ℂ} (h : TendstoLocallyUniformlyOn F g l Set.univ)
    {K : Set ℂ} (hK : IsCompact K) (hg : ContinuousOn g K) (hne : ∀ z ∈ K, g z ≠ 0) :
    ∀ᶠ i in l, ∀ z ∈ K, F i z ≠ 0 := by
  obtain ⟨δ,hδ,hb⟩ := hK.exists_forall_le' hg.norm (fun z hz => norm_pos_iff.mpr (hne z hz))
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (h.mono (Set.subset_univ _))
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) δ hδ] with i hi z hz hzero
  have hd := hi z hz
  rw [dist_eq_norm, hzero, sub_zero] at hd
  exact (hb z hz).not_gt hd

/-- Nearby analytic functions have exactly the same count on every zero-free circular boundary. -/
theorem eventually_analyticZeroCount_eq {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {g : ℂ → ℂ} (h : TendstoLocallyUniformlyOn F g l Set.univ)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) (closedBall c r))
    (hg : AnalyticOnNhd ℂ g (closedBall c r)) (hne : ∀ z ∈ sphere c r, g z ≠ 0) :
    ∀ᶠ i in l, analyticZeroCount (F i) (closedBall c r) = analyticZeroCount g (closedBall c r) := by
  obtain ⟨δ,hδ,hb⟩ := (isCompact_sphere c r).exists_forall_le'
    ((hg.continuousOn.mono sphere_subset_closedBall).norm) (fun z hz => norm_pos_iff.mpr (hne z hz))
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere c r)).mp
    (h.mono (Set.subset_univ _))
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) δ hδ] with i hi
  apply analyticZeroCount_eq_of_boundary_lt hr hg (hF i)
  intro z hz
  have hd := hi z hz
  rw [dist_eq_norm, norm_sub_rev] at hd
  exact hd.trans_le (hb z hz)

/-- All nearby roots in a compact set stay in any open neighborhood of the limit's roots. -/
theorem eventually_roots_mem_open {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {g : ℂ → ℂ} (h : TendstoLocallyUniformlyOn F g l Set.univ)
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hg : ContinuousOn g K)
    (hroots : ∀ z ∈ K, g z = 0 → z ∈ U) :
    ∀ᶠ i in l, ∀ z ∈ K, F i z = 0 → z ∈ U := by
  have hc : IsCompact (K ∩ Uᶜ) := hK.inter_right hU.isClosed_compl
  have hn := eventually_ne_zero_on_compact h hc (hg.mono Set.inter_subset_left)
    (fun z hz he => hz.2 (hroots z hz.1 he))
  filter_upwards [hn] with i hi z hz hzero
  by_contra hnot
  exact hi z ⟨hz,hnot⟩ hzero

/-- A unique zero in a compact set determines the limit of every nearby root selected in that set. -/
theorem tendsto_roots_of_unique_on_compact {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {g : ℂ → ℂ} (h : TendstoLocallyUniformlyOn F g l Set.univ)
    {K : Set ℂ} (hK : IsCompact K) (hg : ContinuousOn g K) (c : ℂ)
    (hunique : ∀ z ∈ K, g z = 0 → z = c) (x : ι → ℂ)
    (hx : ∀ᶠ i in l, x i ∈ K) (hz : ∀ᶠ i in l, F i (x i) = 0) : Tendsto x l (𝓝 c) := by
  apply _root_.tendsto_nhds.mpr
  intro U hU hc
  have he := eventually_roots_mem_open h hK hU hg
    (fun z hz hzero => hunique z hz hzero ▸ hc)
  filter_upwards [he,hx,hz] with i hi hxi hzi
  exact hi (x i) hxi hzi

end NLS.ComplexAnalysis
