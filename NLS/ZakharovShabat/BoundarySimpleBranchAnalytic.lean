import NLS.ZakharovShabat.BoundaryEigenvalues
import NLS.ZakharovShabat.EntirePeriodicProductOrders

/-!
# Analyticity of continuous simple boundary branches

A small circle isolates an algebraically simple boundary eigenvalue. Its
boundary contour projection has rank one, and that rank persists locally.
Any continuous spectral branch through the eigenvalue therefore agrees
locally with the analytic contour trace. This includes central coordinates;
no high-index counting disc is required.
-/

noncomputable section
open Set Complex Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat.BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition)

/-- An admissible circle and the rank of its boundary projection persist on
the reflected parameter subspace. -/
theorem eventually_finrank_contourProjection_eq (hp : p ≠ ⊤)
    (φ : dirichletSubspace (p := p)) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ.val) :
    ∀ᶠ ψ : dirichletSubspace (p := p) in 𝓝 φ,
      sphere c r ⊆ ZakharovShabat.resolventSet hp ψ.val ∧
      Module.finrank ℂ (contourProjection b hp ψ.val c r).range =
        Module.finrank ℂ (contourProjection b hp φ.val c r).range := by
  have hcont := (analyticAt_contourProjection b hp φ.val c r hr hc).continuousAt.comp
    continuous_subtype_val.continuousAt
  have hnear := hcont.preimage_mem_nhds
    (Metric.ball_mem_nhds (contourProjection b hp φ.val c r) zero_lt_one)
  have hcircle : ∀ᶠ ψ : dirichletSubspace (p := p) in 𝓝 φ,
      sphere c r ⊆ ZakharovShabat.resolventSet hp ψ.val :=
    continuous_subtype_val.continuousAt.eventually
      ((isOpen_resolventCircleDomain hp c r).mem_nhds hc)
  filter_upwards [hcircle, hnear] with ψ hψ hnorm
  refine ⟨hψ, ?_⟩
  let : FiniteDimensional ℂ (contourProjection b hp ψ.val c r).range :=
    finiteDimensional_range_contourProjection b hp ψ.val c r hr hψ
  let : FiniteDimensional ℂ (contourProjection b hp φ.val c r).range :=
    finiteDimensional_range_contourProjection b hp φ.val c r hr hc
  exact NLS.ProjectionRank.finrank_eq_of_norm_sub_lt_one _ _
    (contourProjection_idempotent b hp ψ.val ψ.property c r hr hψ)
    (contourProjection_idempotent b hp φ.val φ.property c r hr hc)
    (by simpa only [mem_preimage, Function.comp_apply, mem_ball, dist_eq_norm] using hnorm)

/-- A continuous boundary spectral branch is analytic at every point where
its actual algebraic multiplicity is one. -/
theorem analyticAt_of_continuous_simple_spectral_branch (hp : p ≠ ⊤)
    (f : dirichletSubspace (p := p) → ℂ) (φ : dirichletSubspace (p := p))
    (hf : ContinuousAt f φ)
    (hspec : ∀ ψ, f ψ ∈ spectrum b hp ψ.val ψ.property)
    (hsimple : algebraicMultiplicity b hp φ.val φ.property (f φ) = 1) :
    AnalyticAt ℂ f φ := by
  classical
  obtain ⟨r, hr, hiso⟩ := exists_periodicSpectrum_isolating_closedBall hp φ.val (f φ)
  have hc : sphere (f φ) r ⊆ ZakharovShabat.resolventSet hp φ.val := by
    intro z hz
    have hnot : z ∉ periodicSpectrum hp φ.val := by
      intro hspecz
      have he := hiso z (sphere_subset_closedBall hz) hspecz
      have hd : dist z (f φ) = r := hz
      rw [he, dist_self] at hd
      exact hr.ne hd
    simpa only [periodicSpectrum, mem_compl_iff, not_not] using hnot
  have henclosed : enclosedSpectrum b hp φ.val φ.property (f φ) r = {f φ} := by
    ext z
    rw [mem_enclosedSpectrum, Finset.mem_singleton]
    constructor
    · intro hz
      exact hiso z (ball_subset_closedBall hz.2)
        (spectrum_subset_periodic b hp φ.val φ.property hz.1)
    · intro hz
      subst z
      exact ⟨hspec φ, mem_ball_self hr⟩
  have hrank : Module.finrank ℂ (contourProjection b hp φ.val (f φ) r).range = 1 := by
    rw [finrank_contour_eq_sum_enclosed b hp φ.val φ.property (f φ) r hr.le hc,
      henclosed, Finset.sum_singleton, hsimple]
  apply (analyticAt_contourTrace b hp φ (f φ) r hr.le hc).congr
  have hroot := hf.preimage_mem_nhds (Metric.ball_mem_nhds (f φ) hr)
  filter_upwards [eventually_finrank_contourProjection_eq b hp φ (f φ) r hr.le hc,
    hroot] with ψ hψ hball
  exact contourTrace_eq_of_rank_one b hp ψ.val ψ.property (f φ) (f ψ) r hψ.1
    (hψ.2.trans hrank) ((mem_enclosedSpectrum b hp ψ.val ψ.property (f φ) (f ψ) r).mpr
      ⟨hspec ψ, hball⟩)

end NLS.ZakharovShabat.BoundaryCondition
