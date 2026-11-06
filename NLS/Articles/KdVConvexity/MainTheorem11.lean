import NLS.Articles.KdVConvexity.BasePhysicalFrequencyConstruction
import NLS.Articles.KdVConvexity.PhysicalHstarReality

/-! # Theorem 1.1 with its necessary base-frequency correction

The physical global extension, common-domain physical frequencies, full
minus-six derivative, local analytic inverse and one-radius Hessian bound
are constructed without hypotheses. The preamble's incompatible locally
uniform O(1) estimate on a complex base neighborhood is explicitly excluded.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.Articles.KdVConvexity

/-- Exact positive-index physical data for all assertions of Theorem 1.1,
with the printed uniform base estimate (1.7) corrected by its proved negation.
The Hamiltonian and frequency records retain their full original domains,
physical recovery statements and literal raw-action normalization. -/
structure Theorem11PhysicalData where
  extension : PhysicalHstarExtension
  frequencies : BasePhysicalFrequencyExtension
  domain_compatible : extension.domain ⊆ baseActionInclusion ⁻¹' frequencies.domain
  frequency_identity : ∀ a ∈ extension.domain, ∀ n : ℕ+,
    actionGradient extension.hamiltonian a n=frequencies.frequency n (baseActionInclusion a)-
      ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)
  real_on_cone : ∀ a ∈ positiveQuadrant, (extension.hamiltonian a).im=0
  gradient_zero : actionGradient extension.hamiltonian 0=0
  gradient_derivative_zero : fderiv ℂ (actionGradient extension.hamiltonian) 0=
    (-6 : ℂ) • ContinuousLinearMap.id ℂ ActionSpace
  local_inverse : ∃ V W : Set ActionSpace, IsOpen V ∧ IsOpen W ∧ (0 : ActionSpace) ∈ V ∧
    (0 : ActionSpace) ∈ W ∧ V ⊆ extension.domain ∧ actionGradient extension.hamiltonian '' V=W ∧
    Set.BijOn (actionGradient extension.hamiltonian) V W ∧
    ∃ G : ActionSpace → ActionSpace,
      AnalyticOnNhd ℂ (actionGradient extension.hamiltonian) V ∧ AnalyticOnNhd ℂ G W ∧
      (∀ a ∈ V, G (actionGradient extension.hamiltonian a)=a) ∧
      (∀ b ∈ W, G b ∈ V ∧ actionGradient extension.hamiltonian (G b)=b)
  hessian_bound : ∃ r : ℝ, 0<r ∧ ball (0 : ActionSpace) r ⊆ extension.domain ∧
    (∀ a ∈ ball (0 : ActionSpace) r, ∀ v : ActionSpace, (∀ n : ℕ+, (v n).im=0) →
      (fderiv ℂ (fderiv ℂ extension.hamiltonian) a v v).re ≤ -‖v‖^2) ∧
    StrictConcaveOn ℝ (ball (0 : ActionSpace) r ∩ positiveQuadrant)
      (fun a => (extension.hamiltonian a).re)

/-- The corrected Theorem 1.1, with all physical, spectral, analytic,
action-descent and normalization obligations discharged. -/
theorem theorem_1_1_corrected : Nonempty Theorem11PhysicalData := by
  obtain ⟨B⟩ := nonempty_basePhysicalFrequencyExtension
  obtain ⟨E,hEB,hfreq⟩ := B.exists_compatible_physicalHstarExtension
  exact ⟨⟨E,B,hEB,hfreq,(fun a ha => (E.real_and_nonpositive_on_cone a ha).1),
    E.Taylor_at_zero.2.1,E.Taylor_at_zero.2.2,E.local_gradient_inverse,E.local_hessian_bound_and_strict_concavity⟩⟩

/-- The renormalized frequency vector is analytic as a map into the
actual positive-index Hilbert space on the WHOLE extension domain. -/
theorem Theorem11PhysicalData.analytic_nonlinear_frequency (T : Theorem11PhysicalData) :
    AnalyticOnNhd ℂ (actionGradient T.extension.hamiltonian) T.extension.domain :=
  analyticOnNhd_actionGradient T.extension.hamiltonian T.extension.analytic

/-- Equation (1.7), interpreted on one common complex base neighborhood,
cannot accompany these actual physical frequencies. -/
theorem Theorem11PhysicalData.printed_uniform_base_estimate_impossible (T : Theorem11PhysicalData) :
    ¬ ∃ (N : ℕ) (M : ℝ), ∀ᶠ a : BaseActionSpace in 𝓝 0, ∀ n : ℕ+, N ≤ (n : ℕ) →
      ‖T.frequencies.frequency n a-((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)‖ ≤ M :=
  T.frequencies.not_locally_uniformly_bounded_tail

end NLS.Articles.KdVConvexity
