import NLS.ComplexAnalysis.LimitNonvanishing
import NLS.ComplexAnalysis.AnalyticQuotientUniqueness

/-!
# Nonvanishing locally uniform limits

A finite-order analytic limit cannot acquire a zero inside an open set on
which all entire approximants are nonvanishing. The finite-order hypothesis
excludes the identically zero limit.
-/

noncomputable section
open Filter Topology Metric Set
namespace NLS.ComplexAnalysis

/-- A nonvanishing sequence cannot develop a finite-order analytic zero in its open domain. -/
theorem limit_ne_zero_on_open_of_finite_order (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    {U : Set ℂ} (hU : IsOpen U) {c : ℂ} (hc : c ∈ U)
    (hF : ∀ n, Differentiable ℂ (F n)) (hFn : ∀ n, ∀ z ∈ U, F n z ≠ 0)
    (hg : AnalyticOnNhd ℂ g U) (hfin : analyticOrderAt g c ≠ ⊤)
    (h : TendstoLocallyUniformlyOn F g atTop U) : g c ≠ 0 := by
  have hiso : ∀ᶠ z in 𝓝 c, z ≠ c → g z ≠ 0 :=
    eventually_nhdsWithin_iff.mp (eventually_ne_zero_of_finite_analyticOrder (hg c hc) hfin)
  have hmem : ∀ᶠ z in 𝓝 c, z ∈ U := hU.mem_nhds hc
  obtain ⟨r, hr, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hmem.and hiso)
  have hsub : closedBall c r ⊆ U := fun z hz => (hb hz).1
  have hn (z : ℂ) (hz : z ∈ sphere c r) : g z ≠ 0 := by
    apply (hb (sphere_subset_closedBall hz)).2
    intro he
    subst z
    have hzero : (0 : ℝ) = r := by simpa only [mem_sphere, dist_self] using hz
    exact (ne_of_lt hr) hzero
  exact limit_ne_zero_of_nonzero_on_closedBall F g c r hr hF
    (fun n z hz => hFn n z (hsub hz))
    (hg.continuousOn.mono (sphere_subset_closedBall.trans hsub)) hn
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere c r)).mp
      (h.mono (sphere_subset_closedBall.trans hsub))) (h.tendsto_at hc)

end NLS.ComplexAnalysis
