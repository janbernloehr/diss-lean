import NLS.Articles.KdVKdV2Frequencies.ActualHilbertWeakFrequencyAgreement
import NLS.Articles.KdVKdV2Frequencies.GlobalWeakFrequencyNormalization

/-! EVERY globally analytic weak scalar family with actual native
Hamiltonian recovery agrees with the actual physical Hilbert gradient on
the ENTIRE nonnegative Hilbert action cone, including nonsummable actions. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
namespace NLS.Articles.KdVKdV2Frequencies

theorem global_scalar_frequency_eq_physical_hilbert_gradient
    (D : GlobalRoughAbelianForwardData) (E : PhysicalHstarExtension)
    (V : Set (Coeff 1)) (G : ℕ+ → Coeff 1 → ℂ)
    (hV : IsOpen V) (hCV : Coeff.nonnegativeLocus 1⊆V)
    (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)), ∀ n : ℕ+,
      G n (weakActionEnumeration (D.nativeWeakActionSequence 1 q))=
        (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3)
    (a : ActionSpace) (ha : a∈positiveQuadrant) (n : ℕ+) :
    G n (weakActionEnumeration (hilbertWeakActions a))=actionGradient E.hamiltonian a n := by
  let J := weakActionEnumeration.comp hilbertWeakActions
  let W := E.domain∩J ⁻¹' V
  have hW : IsOpen W := E.isOpen.inter (hV.preimage J.continuous)
  have hWa : a∈W := ⟨E.contains_cone ha,hCV (weakActionEnumeration_nonnegative _ (hilbertWeakActions_nonnegative a ha))⟩
  have hf : ContinuousOn (fun x => G n (J x)) W :=
    (show AnalyticOnNhd ℂ (fun x => G n (J x)) W from
      fun x hx => (hG n _ hx.2).comp (J.analyticAt x)).continuousOn
  have hg : ContinuousOn (fun x : ActionSpace => actionGradient E.hamiltonian x n) W :=
    (show AnalyticOnNhd ℂ (fun x : ActionSpace => actionGradient E.hamiltonian x n) W from
      fun x hx => ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n).analyticAt _).comp
        (analyticOnNhd_actionGradient _ E.analytic x hx.1)).continuousOn
  apply eqOn_positive_of_original_domain_agreement _ _ W hW hf hg ?_ a hWa ha
  intro x _hx hxp
  obtain ⟨b,hb,hbx⟩ := original_domain_has_weighted_representative x hxp
  let r := ‖hilbertWeakActions (originalActionInclusion b)‖+1
  have hball : hilbertWeakActions (originalActionInclusion b)∈ball (0 : Coeff 1) r := by
    rw [mem_ball_zero_iff]
    dsimp only [r]
    linarith
  have he := D.weakFrequency_eq_gradient_on_original_actions E r
    (fun n y => G n (weakActionEnumeration y)) (fun q _hq n => hrec q n) ⟨b,hb⟩ hball n
  simpa only [J,ContinuousLinearMap.comp_apply,hbx] using he

end NLS.Articles.KdVKdV2Frequencies
