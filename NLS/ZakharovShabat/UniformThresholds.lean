import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Uniform thresholds from pulled-back limits

A limit along the pullback of the real at-top filter gives a bound valid at
every point whose height exceeds one threshold. No choice of a particular
path or nontriviality assumption on that filter is needed.
-/

noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat

/-- Unpack an eventual assertion into a uniform real threshold. -/
theorem exists_threshold_of_eventually_comap_atTop {α : Type*} (h : α → ℝ)
    {P : α → Prop} (hP : ∀ᶠ a in comap h atTop, P a) :
    ∃ R : ℝ, ∀ a, R ≤ h a → P a := by
  obtain ⟨s, hs, hsP⟩ := mem_comap.mp hP
  obtain ⟨R, hR⟩ := mem_atTop_sets.mp hs
  exact ⟨R, fun a ha => hsP (hR _ ha)⟩

/-- A complex-valued limit of one gives a uniform upper bound of two. -/
theorem exists_threshold_norm_le_two {α : Type*} (h : α → ℝ) (f : α → ℂ)
    (hf : Tendsto f (comap h atTop) (𝓝 1)) :
    ∃ R : ℝ, ∀ a, R ≤ h a → ‖f a‖ ≤ 2 := by
  apply exists_threshold_of_eventually_comap_atTop h
  have hn : Tendsto (fun a => ‖f a‖) (comap h atTop) (𝓝 1) := by
    simpa using hf.norm
  filter_upwards [hn.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))] with a ha
  exact ha.le

/-- The same limit gives a uniform positive lower bound, including nonvanishing. -/
theorem exists_threshold_half_le_norm {α : Type*} (h : α → ℝ) (f : α → ℂ)
    (hf : Tendsto f (comap h atTop) (𝓝 1)) :
    ∃ R : ℝ, ∀ a, R ≤ h a → (1 : ℝ)/2 ≤ ‖f a‖ := by
  apply exists_threshold_of_eventually_comap_atTop h
  have hn : Tendsto (fun a => ‖f a‖) (comap h atTop) (𝓝 1) := by
    simpa using hf.norm
  filter_upwards [hn.eventually (lt_mem_nhds (by norm_num : (1 : ℝ)/2 < 1))] with a ha
  exact ha.le

end NLS.ZakharovShabat
