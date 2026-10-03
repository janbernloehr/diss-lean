import NLS.ZakharovShabat.ResolventCompactConvergence
import NLS.ZakharovShabat.ContourSpectrum
import NLS.FunctionalAnalysis.ProjectionRank

/-! # Stability of spectral cluster multiplicities under coefficient limits

Bounded coefficientwise convergence gives norm convergence of contour
projections and hence eventual equality of their finite ranks. Individual
eigenvalues may split or coalesce; total enclosed algebraic multiplicity stays
fixed. No convergence in the potential norm is assumed.
-/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Contour projection rank is eventually constant under bounded coefficient
limits, with eventual common resolvent membership of the entire circle. -/
theorem eventually_finrank_resolventCircleIntegral_eq_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → PairSpace p) (ψ : PairSpace p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp ψ) :
    ∀ᶠ k in l, sphere c r ⊆ resolventSet hp (φ k) ∧
      Module.finrank ℂ (resolventCircleIntegral hp (φ k) c r).range =
        Module.finrank ℂ (resolventCircleIntegral hp ψ c r).range := by
  have ht := tendsto_resolventCircleIntegral_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂ c r hr hc
  have hnear := ht.eventually (Metric.ball_mem_nhds _ zero_lt_one)
  have hev := eventually_compact_subset_resolventSet_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂
    (sphere c r) (isCompact_sphere c r) hc
  filter_upwards [hev, hnear] with k hk hnorm
  refine ⟨hk, ?_⟩
  let : FiniteDimensional ℂ (resolventCircleIntegral hp (φ k) c r).range :=
    finiteDimensional_range_resolventCircleIntegral hp (φ k) c r hr hk
  let : FiniteDimensional ℂ (resolventCircleIntegral hp ψ c r).range :=
    finiteDimensional_range_resolventCircleIntegral hp ψ c r hr hc
  apply NLS.ProjectionRank.finrank_eq_of_norm_sub_lt_one _ _
    (resolventCircleIntegral_idempotent hp (φ k) c r hr hk)
    (resolventCircleIntegral_idempotent hp ψ c r hr hc)
  simpa only [Metric.mem_ball, dist_eq_norm] using hnorm

/-- A spectral-free limit circle eventually encloses exactly the same total
algebraic multiplicity for every member of a bounded coefficientwise limit. -/
theorem eventually_sum_enclosed_multiplicity_eq_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → PairSpace p) (ψ : PairSpace p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp ψ) :
    ∀ᶠ k in l,
      ∑ z ∈ enclosedPeriodicSpectrum hp (φ k) c r, periodicAlgebraicMultiplicity hp (φ k) z =
        ∑ z ∈ enclosedPeriodicSpectrum hp ψ c r, periodicAlgebraicMultiplicity hp ψ z := by
  filter_upwards [eventually_finrank_resolventCircleIntegral_eq_of_bounded_coefficientwise
    hp hp1 φ ψ hb ht₁ ht₂ c r hr hc] with k hk
  rw [← finrank_range_resolventCircleIntegral hp (φ k) c r hr hk.1,
    ← finrank_range_resolventCircleIntegral hp ψ c r hr hc]
  exact hk.2

end NLS.ZakharovShabat
