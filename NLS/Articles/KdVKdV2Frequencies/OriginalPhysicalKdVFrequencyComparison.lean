import NLS.Articles.KdVKdV2Frequencies.OriginalPhysicalKdVEnergyComparison
import NLS.Articles.KdVConvexity.PhysicalTaylorAtZero

/-! # The actual KdV frequencies in the global physical Hilbert extension

Equality of the independent full physical energies determines every positive
raw action derivative, including closed gaps. Consequently the Hilbert-valued
gradient extends this article's actual frequency correction on its ENTIRE
original native action cone, with the exact full minus-six Taylor operator.
Compactness of the derivative at other actions and the larger weak action
domain remain separate obligations in the main theorem.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.Articles.KdVConvexity
namespace NLS.Articles.KdVKdV2Frequencies
namespace GlobalRoughAbelianForwardData

/-- The independent physical frequency and the actual original native KdV
frequency agree with precisely the SAME raw action direction and labels. -/
theorem originalKdVFrequency_eq_originalPhysicalFrequency
    (D : GlobalRoughAbelianForwardData)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1) (n : ℕ+) :
    (D.originalKdVFrequency a n : ℂ)=originalPhysicalFrequency
      ⟨physicalHilbertActionReindex a.val,physicalHilbertActionReindex_nonnegative a.val a.property.1⟩ n := by
  obtain ⟨F⟩ := nonempty_originalHierarchyActionFactor D 1 3 (by norm_num)
  let E := Classical.choice nonempty_physicalHstarExtension
  let b : WeightedCoeff.nonnegativeLocus originalActionWeight 1 :=
    ⟨physicalHilbertActionReindex a.val,physicalHilbertActionReindex_nonnegative a.val a.property.1⟩
  have hE : AnalyticAt ℂ E.originalFullEnergy (physicalHilbertActionReindex a.val) :=
    E.originalFullEnergy_analytic b.val (E.originalDomain_contains_cone b)
  have hG : AnalyticAt ℂ (fun x => E.originalFullEnergy (physicalHilbertActionReindex x)) a.val :=
    hE.comp (physicalHilbertActionReindex.analyticAt a.val)
  have he := WeightedCoeff.fderiv_single_eq_of_positive_action_recovery
    F.value (fun x => E.originalFullEnergy (physicalHilbertActionReindex x)) a.val a.property n
    (by exact_mod_cast n.pos)
    (F.analytic a.val (F.nonnegative_subset_domain a.property.1)).differentiableAt hG.differentiableAt
    (by
      intro c hc
      rw [F.value_eq_physical_actionHamiltonian ⟨c,hc⟩,
        E.originalFullEnergy_eq_physical
          ⟨physicalHilbertActionReindex c,physicalHilbertActionReindex_nonnegative c hc.1⟩,
        D.physicalActionEnergy_eq_original ⟨c,hc⟩])
  have hcomp := hE.differentiableAt.hasFDerivAt.comp a.val physicalHilbertActionReindex.hasFDerivAt
  have hfd : fderiv ℂ (fun x => E.originalFullEnergy (physicalHilbertActionReindex x)) a.val=
      (fderiv ℂ E.originalFullEnergy (physicalHilbertActionReindex a.val)).comp physicalHilbertActionReindex :=
    hcomp.fderiv
  rw [hfd] at he
  change _=fderiv ℂ E.originalFullEnergy b.val
    (physicalHilbertActionReindex (WeightedCoeff.single (Weight.sobolev 3) (n : ℤ) 1)) at he
  rw [physicalHilbertActionReindex_single] at he
  rw [originalKdVFrequency,D.originalHierarchyFrequency_eq_factor_derivative 1 3 (by norm_num) F a n]
  exact he.trans (congrArg (fun L : OriginalActionSpace →L[ℂ] ℂ =>
    L (WeightedCoeff.single originalActionWeight (actionIndexEquiv.symm n) 1))
      (originalPhysicalEnergyDifferential_eq E b)).symm

/-- The actual article frequencies are the coordinates of the physical
Hilbert gradient after subtracting exactly the printed cubic dispersion. -/
theorem originalKdVFrequency_correction_eq_gradient
    (D : GlobalRoughAbelianForwardData) (E : PhysicalHstarExtension)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1) (n : ℕ+) :
    (D.originalKdVFrequency a n : ℂ)-((2*Real.pi*(n : ℝ))^3 : ℝ)=
      actionGradient E.hamiltonian (originalActionInclusion (physicalHilbertActionReindex a.val)) n := by
  rw [D.originalKdVFrequency_eq_originalPhysicalFrequency,
    originalPhysicalFrequency_eq_gradient E]
  have hdisp : (8*(n : ℝ)^3*Real.pi^3 : ℝ)=(2*Real.pi*(n : ℝ))^3 := by ring
  rw [hdisp,add_sub_cancel_left]

/-- A genuine GLOBAL analytic Hilbert-valued extension of this article's
actual KdV correction, with its full bounded Taylor derivative at zero.
The domain contains the ENTIRE nonnegative Hilbert cone. Agreement holds
on EVERY original cubic-weight action point, without support/gap premises. -/
theorem exists_global_hilbert_actual_kdv_frequency_with_Taylor
    (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set ActionSpace, ∃ H : ActionSpace → ℂ, ∃ G : ActionSpace → ActionSpace,
      IsOpen V ∧ positiveQuadrant ⊆ V ∧ AnalyticOnNhd ℂ H V ∧ AnalyticOnNhd ℂ G V ∧
      H 0=0 ∧ G 0=0 ∧
      fderiv ℂ G 0=(-6 : ℂ) • ContinuousLinearMap.id ℂ ActionSpace ∧
      (∀ a ∈ V, ∀ v : ActionSpace, fderiv ℂ H a v=∑' n : ℕ+, G a n*v n) ∧
      ∀ a : WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1, ∀ n : ℕ+,
        G (originalActionInclusion (physicalHilbertActionReindex a.val)) n=
          (D.originalKdVFrequency a n : ℂ)-((2*Real.pi*(n : ℝ))^3 : ℝ) := by
  obtain ⟨E,hzero,hgrad,hderiv⟩ := exists_physicalHstarExtension_with_Taylor_at_zero
  exact ⟨E.domain,E.hamiltonian,actionGradient E.hamiltonian,E.isOpen,E.contains_cone,E.analytic,
    analyticOnNhd_actionGradient _ E.analytic,hzero,hgrad,hderiv,
    (fun a _ v => fderiv_eq_tsum_actionGradient _ a v),
    fun a n => (D.originalKdVFrequency_correction_eq_gradient E a n).symm⟩

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
