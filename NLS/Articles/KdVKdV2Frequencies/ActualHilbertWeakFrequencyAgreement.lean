import NLS.Articles.KdVKdV2Frequencies.NativeHilbertWeakActionComparison
import NLS.Articles.KdVKdV2Frequencies.CommonWeakKdVActionFrequency
import NLS.ComplexAnalysis.CommonConeWeakNeighborhood
import Mathlib.Analysis.Analytic.Uniqueness

/-! # One common complex domain for the ACTUAL Hilbert and weak KdV corrections

The SAME scalar weak-action functions agree with the SAME physical Hilbert
gradient on an intersection of full complex open domains, chosen BEFORE all
indices. The Hilbert domain still contains the ENTIRE nonnegative cone.
The weak domain here is a ball near zero, not the still-open global weak
cone neighborhood required by the complete main theorem.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVConvexity
namespace NLS.Articles.KdVKdV2Frequencies

private theorem convex_hilbert_positiveQuadrant : Convex ℝ positiveQuadrant := by
  intro a ha b hb u v hu hv _ n
  change (u • a n+v • b n).im=0 ∧ 0≤(u • a n+v • b n).re
  constructor
  · simp [(ha n).1,(hb n).1]
  · simpa using add_nonneg (mul_nonneg hu (ha n).2) (mul_nonneg hv (hb n).2)

namespace GlobalRoughAbelianForwardData

/-- Reality holds on the ENTIRE nonnegative Hilbert cone, even beyond
cubic-weight summability. Literal finite-action limits preserve the actual
native frequency values and all closed coordinates. -/
theorem physicalHilbertGradient_real (D : GlobalRoughAbelianForwardData)
    (E : PhysicalHstarExtension) (a : ActionSpace) (ha : a∈positiveQuadrant) (n : ℕ+) :
    (actionGradient E.hamiltonian a n).im=0 := by
  have hg : AnalyticOnNhd ℂ (fun x : ActionSpace => actionGradient E.hamiltonian x n) E.domain :=
    fun x hx => ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n).analyticAt _).comp
      (analyticOnNhd_actionGradient _ E.analytic x hx)
  have hf : ContinuousOn (fun x : ActionSpace => ((actionGradient E.hamiltonian x n).im : ℂ)) E.domain :=
    fun x hx => (Complex.continuous_ofReal.continuousAt.comp
      (Complex.continuous_im.continuousAt.comp (hg x hx).continuousAt)).continuousWithinAt
  have he := eqOn_positive_of_original_domain_agreement
    (fun x : ActionSpace => ((actionGradient E.hamiltonian x n).im : ℂ)) (fun _ => 0)
      E.domain E.isOpen hf continuousOn_const (by
        intro x _ hx
        obtain ⟨b,hb,hbx⟩ := original_domain_has_weighted_representative x hx
        let c : WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1 :=
          ⟨originalHilbertActionLift b,originalHilbertActionLift_positive b hb⟩
        have hc := D.originalKdVFrequency_correction_eq_gradient E c n
        rw [physicalHilbertActionReindex_lift,hbx] at hc
        have hi := congrArg Complex.im hc.symm
        simpa only [sub_im,ofReal_im,sub_self,ofReal_zero] using congrArg Complex.ofReal hi)
      a (E.contains_cone ha) ha
  exact_mod_cast he

/-- Every weak factor recovering the true native frequencies agrees with
the physical Hilbert gradient on the ENTIRE original positive action cone
in its domain, and hence fixes its complex germ at zero. -/
theorem weakFrequency_eventuallyEq_HilbertGradient_zero
    (D : GlobalRoughAbelianForwardData) (E : PhysicalHstarExtension)
    (ρ : ℝ) (hρ : 0<ρ) (g : ℕ+ → Coeff 1 → ℂ)
    (hg : ∀ n, AnalyticOnNhd ℂ (g n) (ball (0 : Coeff 1) ρ))
    (hrec : ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
      D.nativeWeakActionSequence 1 q∈ball (0 : Coeff 1) ρ → ∀ n : ℕ+,
        g n (D.nativeWeakActionSequence 1 q)=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3)
    (n : ℕ+) :
    (fun a : ActionSpace => g n (hilbertWeakActions a)) =ᶠ[𝓝 0]
      (fun a => actionGradient E.hamiltonian a n) := by
  let U := E.domain∩hilbertWeakActions ⁻¹' ball (0 : Coeff 1) ρ
  have hU : IsOpen U := E.isOpen.inter (isOpen_ball.preimage hilbertWeakActions.continuous)
  have hf : AnalyticOnNhd ℂ (fun a : ActionSpace => g n (hilbertWeakActions a)) U :=
    fun a ha => (hg n _ ha.2).comp (hilbertWeakActions.analyticAt a)
  have hG : AnalyticOnNhd ℂ (fun a : ActionSpace => actionGradient E.hamiltonian a n) U :=
    fun a ha => ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n).analyticAt _).comp
      (analyticOnNhd_actionGradient _ E.analytic a ha.1)
  apply eventuallyEq_of_original_domain_agreement _ _ U hU hf hG ?_ 0
    ⟨E.contains_cone zero_mem_positiveQuadrant,by
      change hilbertWeakActions (0 : ActionSpace)∈ball (0 : Coeff 1) ρ
      rw [map_zero]
      exact mem_ball_self hρ⟩ zero_mem_positiveQuadrant
  intro a ha hapos
  obtain ⟨b,hb,hba⟩ := original_domain_has_weighted_representative a hapos
  rw [←hba] at ha ⊢
  exact D.weakFrequency_eq_gradient_on_original_actions E ρ g hrec ⟨b,hb⟩ ha.2 n

/-- ONE open Hilbert neighborhood of the ENTIRE nonnegative cone and ONE
weak-action ball, both chosen BEFORE EVERY n, support the SAME actual
frequency corrections on their FULL COMPLEX intersection. The Hilbert
gradient is real on the entire positive cone and has FULL derivative -6Id
at zero. Original frequencies and raw weak weights are retained exactly. -/
theorem exists_common_complex_hilbert_weak_kdv_frequency
    (D : GlobalRoughAbelianForwardData) :
    ∃ ρ : ℝ, ∃ g : ℕ+ → Coeff 1 → ℂ, ∃ E : PhysicalHstarExtension, ∃ V : Set ActionSpace,
      0<ρ ∧ IsOpen V ∧ positiveQuadrant⊆V ∧ V⊆E.domain ∧
      (∀ n, AnalyticOnNhd ℂ (g n) (ball (0 : Coeff 1) ρ)) ∧
      (∀ b∈ball (0 : Coeff 1) ρ, b∈Coeff.nonnegativeLocus 1 → ∀ n, (g n b).im=0) ∧
      AnalyticOnNhd ℂ (actionGradient E.hamiltonian) V ∧
      (∀ a∈positiveQuadrant, ∀ n, (actionGradient E.hamiltonian a n).im=0) ∧
      actionGradient E.hamiltonian 0=0 ∧
      fderiv ℂ (actionGradient E.hamiltonian) 0=(-6 : ℂ) • ContinuousLinearMap.id ℂ ActionSpace ∧
      (∀ a∈V, hilbertWeakActions a∈ball (0 : Coeff 1) ρ → ∀ n,
        g n (hilbertWeakActions a)=actionGradient E.hamiltonian a n) ∧
      (∀ a : WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1, ∀ n,
        actionGradient E.hamiltonian (originalActionInclusion (physicalHilbertActionReindex a.val)) n=
          (D.originalKdVFrequency a n : ℂ)-((2*Real.pi*(n : ℝ))^3 : ℝ)) ∧
      ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
        D.nativeWeakActionSequence 1 q∈ball (0 : Coeff 1) ρ → ∀ n,
          g n (D.nativeWeakActionSequence 1 q)=
            (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3 := by
  obtain ⟨r,g,hr,hg,hreal,hrec⟩ := D.exists_common_kdv_weak_action_frequency
  let E := Classical.choice nonempty_physicalHstarExtension
  obtain ⟨V,hV,hcone,hVE,hcommon⟩ :=
    NLS.ComplexAnalysis.exists_open_cone_weak_component_neighborhood hilbertWeakActions
      positiveQuadrant E.domain convex_hilbert_positiveQuadrant zero_mem_positiveQuadrant
      E.isOpen E.contains_cone r hr
  have hsub : ball (0 : Coeff 1) (r/2)⊆ball (0 : Coeff 1) r := ball_subset_ball (by linarith)
  have ht := E.Taylor_at_zero
  refine ⟨r/2,g,E,V,by positivity,hV,hcone,hVE,(fun n => (hg n).mono hsub),
    (fun b hb hpos => hreal b (hsub hb) hpos),
    (analyticOnNhd_actionGradient _ E.analytic).mono hVE,
    (fun a ha n => D.physicalHilbertGradient_real E a ha n),ht.2.1,ht.2.2,?_,
    (fun a n => (D.originalKdVFrequency_correction_eq_gradient E a n).symm),
    (fun q hq n => hrec q (hsub hq) n)⟩
  intro a ha hweak n
  let U := E.domain∩hilbertWeakActions ⁻¹' ball (0 : Coeff 1) r
  let W := connectedComponentIn U (0 : ActionSpace)
  have hWsub : W⊆U := connectedComponentIn_subset U 0
  have hf : AnalyticOnNhd ℂ (fun b : ActionSpace => g n (hilbertWeakActions b)) W :=
    fun b hb => (hg n _ (hWsub hb).2).comp (hilbertWeakActions.analyticAt b)
  have hG : AnalyticOnNhd ℂ (fun b : ActionSpace => actionGradient E.hamiltonian b n) W :=
    fun b hb => ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n).analyticAt _).comp
      (analyticOnNhd_actionGradient _ E.analytic b (hWsub hb).1)
  have h0W : (0 : ActionSpace)∈W := mem_connectedComponentIn
    ⟨E.contains_cone zero_mem_positiveQuadrant,by
      change hilbertWeakActions (0 : ActionSpace)∈ball (0 : Coeff 1) r
      rw [map_zero]
      exact mem_ball_self hr⟩
  exact hf.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_connectedComponentIn h0W
    (D.weakFrequency_eventuallyEq_HilbertGradient_zero E r hr g hg hrec n)
      (hcommon ⟨ha,hweak⟩)

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
