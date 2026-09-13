import NLS.ComplexAnalysis.Rouche
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Stability of isolated analytic orders

When all zeros in a fixed closed disc lie at its center, Rouché's theorem
identifies analytic order with the nearby finite approximants' orders.
-/

noncomputable section
open Filter Topology Metric
namespace NLS.ComplexAnalysis

/-- A disc containing no zeros other than its center has zero count equal to the center's order. -/
theorem analyticZeroCount_eq_order_of_isolated (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hz : ∀ z ∈ closedBall c r, f z = 0 → z = c) :
    analyticZeroCount f (closedBall c r) = analyticOrderNatAt f c := by
  classical
  rw [analyticZeroCount_eq_sum {c}]
  · simp
  · intro z hzc
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hzc
    simpa only [hzc] using mem_closedBall_self hr
  · rintro z ⟨hzb,hz0⟩
    simpa only [Finset.coe_singleton, Set.mem_singleton_iff] using hz z hzb hz0

/-- Uniform convergence on a zero-free boundary fixes the isolated center's order eventually. -/
theorem eventually_analyticOrderNatAt_eq_of_isolated (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hF : ∀ n, AnalyticOnNhd ℂ (F n) (closedBall c r))
    (hg : AnalyticOnNhd ℂ g (closedBall c r))
    (hFz : ∀ n, ∀ z ∈ closedBall c r, F n z = 0 → z = c)
    (hgz : ∀ z ∈ closedBall c r, g z = 0 → z = c)
    (h : TendstoUniformlyOn F g atTop (sphere c r)) :
    ∀ᶠ n : ℕ in atTop, analyticOrderNatAt (F n) c = analyticOrderNatAt g c := by
  have hgn : ∀ z ∈ sphere c r, g z ≠ 0 := by
    intro z hz hz0
    have he := hgz z (sphere_subset_closedBall hz) hz0
    subst z
    have hz0 : (0 : ℝ) = r := by simpa only [mem_sphere, dist_self] using hz
    exact (ne_of_lt hr) hz0
  obtain ⟨δ,hδ,hbound⟩ := (isCompact_sphere c r).exists_forall_le'
    ((hg.continuousOn.mono sphere_subset_closedBall).norm)
    (fun z hz => norm_pos_iff.mpr (hgn z hz))
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp h) δ hδ] with n hn
  have he := analyticZeroCount_eq_of_boundary_lt hr hg (hF n) (fun z hz => by
    have hd := hn z hz
    rw [dist_eq_norm, norm_sub_rev] at hd
    exact hd.trans_le (hbound z hz))
  rwa [analyticZeroCount_eq_order_of_isolated (F n) c r hr.le (hFz n),
    analyticZeroCount_eq_order_of_isolated g c r hr.le hgz] at he

/-- Isolation on a positive-radius disc also excludes infinite analytic order. -/
theorem analyticOrderAt_ne_top_of_isolated (g : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (closedBall c r))
    (hgz : ∀ z ∈ closedBall c r, g z = 0 → z = c) : analyticOrderAt g c ≠ ⊤ := by
  obtain ⟨b,hb⟩ := (NormedSpace.sphere_nonempty (E := ℂ) (x := c)).mpr hr.le
  have hbc : b ≠ c := by
    intro he
    subst b
    have hz0 : (0 : ℝ) = r := by simpa only [mem_sphere, dist_self] using hb
    exact (ne_of_lt hr) hz0
  have hbn : g b ≠ 0 := fun hb0 => hbc (hgz b (sphere_subset_closedBall hb) hb0)
  exact analyticOrderAt_ne_top_on_connected (convex_closedBall c r).isPreconnected hg
    (sphere_subset_closedBall hb) hbn (mem_closedBall_self hr.le)

end NLS.ComplexAnalysis
