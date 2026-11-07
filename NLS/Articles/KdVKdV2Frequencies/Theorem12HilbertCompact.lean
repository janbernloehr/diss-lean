import NLS.Articles.KdVKdV2Frequencies.PhysicalHilbertFrequencyCompact
import NLS.Articles.KdVKdV2Frequencies.GlobalHilbertWeakFrequencyAgreement

/-! The COMPLETE Hilbert target and compact derivative clause
Theorem 1.2(iv), for the ACTUAL physical frequency on the ENTIRE original
positive-index ell2 action cone, with the original correction +6Id. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
namespace NLS.Articles.KdVKdV2Frequencies

theorem GlobalRoughAbelianForwardData.theorem_1_2_iv
    (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set (Coeff 1), ∃ G : ℕ+ → Coeff 1 → ℂ, ∃ E : PhysicalHstarExtension,
      IsOpen V ∧ Coeff.nonnegativeLocus 1⊆V ∧ (∀ n, AnalyticOnNhd ℂ (G n) V) ∧
      (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)), ∀ n : ℕ+,
        G n (weakActionEnumeration (D.nativeWeakActionSequence 1 q))=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3) ∧
      IsOpen E.domain ∧ positiveQuadrant⊆E.domain ∧
      AnalyticOnNhd ℂ (actionGradient E.hamiltonian) E.domain ∧
      (∀ a∈positiveQuadrant, ∀ n : ℕ+,
        G n (weakActionEnumeration (hilbertWeakActions a))=actionGradient E.hamiltonian a n) ∧
      (∀ a∈positiveQuadrant, ∀ n : ℕ+, (actionGradient E.hamiltonian a n).im=0) ∧
      ∀ a∈positiveQuadrant,
        IsCompactOperator (fderiv ℂ (actionGradient E.hamiltonian) a+
          (6 : ℂ) • ContinuousLinearMap.id ℂ ActionSpace) := by
  obtain ⟨V,G,hV,hCV,hG,hrec⟩ := exists_global_physical_frequency_action_corrections D
  let E := Classical.choice nonempty_physicalHstarExtension
  have hnative := global_physical_family_native_recovery D G hrec
  exact ⟨V,G,E,hV,hCV,hG,hnative,E.isOpen,E.contains_cone,
    analyticOnNhd_actionGradient E.hamiltonian E.analytic,
    (fun a ha n => global_scalar_frequency_eq_physical_hilbert_gradient D E V G hV hCV hG hnative a ha n),
    (fun a ha n => D.physicalHilbertGradient_real E a ha n),
    (fun a ha => physical_hilbert_corrected_gradient_compact D E a ha)⟩

end NLS.Articles.KdVKdV2Frequencies
