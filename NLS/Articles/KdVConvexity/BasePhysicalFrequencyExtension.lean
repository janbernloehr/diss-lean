import NLS.Articles.KdVConvexity.BaseFrequencyBoundObstruction
import NLS.Articles.KdVConvexity.PhysicalLocalConsequences
import NLS.Articles.KdVConvexity.PhysicalTaylorExpansion

/-! # The exact remaining frequency construction for Theorem 1.1

This record specifies coordinatewise analyticity and recovery of the actual
physical energy derivatives on the original weighted action cone. It does
not include the incompatible locally uniform O(1) estimate printed in (1.7).
No nonemptiness theorem for this record is asserted here.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.Articles.KdVConvexity

structure BasePhysicalFrequencyExtension where
  domain : Set BaseActionSpace
  frequency : ℕ+ → BaseActionSpace → ℂ
  isOpen : IsOpen domain
  contains_cone : WeightedCoeff.nonnegativeLocus baseActionWeight 1 ⊆ domain
  analytic : ∀ n, AnalyticOnNhd ℂ (frequency n) domain
  physical_agreement : ∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1, ∀ n : ℕ+,
    frequency n (baseActionInclusion (originalActionInclusion b.val))=originalPhysicalFrequency b n

namespace BasePhysicalFrequencyExtension

/-- Once the remaining actual base family is constructed, one physical
Hilbert extension has the simultaneous frequency identity on its WHOLE
domain. Shrinking retains the entire positive cone and all physical values. -/
theorem exists_compatible_physicalHstarExtension (B : BasePhysicalFrequencyExtension) :
    ∃ E : PhysicalHstarExtension, E.domain ⊆ baseActionInclusion ⁻¹' B.domain ∧
      ∀ a ∈ E.domain, ∀ n : ℕ+,
        actionGradient E.hamiltonian a n=B.frequency n (baseActionInclusion a)-
          ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ) := by
  obtain ⟨D⟩ := nonempty_physicalHstarExtension
  obtain ⟨V,hV,hpos,hsub,he⟩ := exists_common_physical_frequency_domain D B.domain B.isOpen
    B.contains_cone B.frequency B.analytic B.physical_agreement
  let E : PhysicalHstarExtension := ⟨V,D.hamiltonian,hV,hpos,
    D.analytic.mono (fun a ha => (hsub ha).1),D.physical_agreement⟩
  exact ⟨E,fun a ha => (hsub ha).2,he⟩

theorem derivative_norm_lower_bound (B : BasePhysicalFrequencyExtension) (n : ℕ+) :
    6*(1+(n : ℝ)) ≤ ‖fderiv ℂ (B.frequency n) 0‖ :=
  physical_base_frequency_derivative_norm_lower_bound B.domain B.isOpen B.contains_cone
    B.frequency B.analytic B.physical_agreement n

theorem not_locally_uniformly_bounded_tail (B : BasePhysicalFrequencyExtension) :
    ¬ ∃ (N : ℕ) (M : ℝ), ∀ᶠ a : BaseActionSpace in 𝓝 0, ∀ n : ℕ+, N ≤ (n : ℕ) →
      ‖B.frequency n a-((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)‖ ≤ M :=
  not_locally_uniformly_bounded_physical_base_frequency_tail B.domain B.isOpen B.contains_cone
    B.frequency B.analytic B.physical_agreement

end BasePhysicalFrequencyExtension
end NLS.Articles.KdVConvexity
