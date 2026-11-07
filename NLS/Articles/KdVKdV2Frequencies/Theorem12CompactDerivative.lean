import NLS.Articles.KdVKdV2Frequencies.OriginalPositiveFrequencyCompact
import NLS.Articles.KdVKdV2Frequencies.Theorem12IntermediateRegularities

/-! The COMPLETE compact derivative clause Theorem 1.2(ii).
The action and target space is the ORIGINAL positive-frequency weighted
ell1 space, with its literal raw coordinates and exact weighted norm.
One actual weak frequency family calibrates every regularity and action. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem GlobalRoughAbelianForwardData.theorem_1_2_ii
    (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set (Coeff 1), ∃ G : ℕ+ → Coeff 1 → ℂ,
      IsOpen V ∧ Coeff.nonnegativeLocus 1⊆V ∧ (∀ n, AnalyticOnNhd ℂ (G n) V) ∧
      (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)), ∀ n : ℕ+,
        G n (weakActionEnumeration (D.nativeWeakActionSequence 1 q))=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3) ∧
      ∀ s : ℝ, ∀ hs0 : -1<s, ∀ _hs1 : s< -1/2,
        ∃ U : Set (WeightedCoeff.positiveSupportedSubmodule (Weight.sobolev (2*s+1))),
          ∃ F : WeightedCoeff.positiveSupportedSubmodule (Weight.sobolev (2*s+1)) →
            WeightedCoeff.positiveSupportedSubmodule (Weight.sobolev (2*s+1)),
            IsOpen U ∧
            {a | a.val∈WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*s+1)) 1}⊆U ∧
            AnalyticOnNhd ℂ F U ∧
            (∀ a, a.val∈WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*s+1)) 1 → ∀ n : ℕ+,
              (F a).val.val (n : ℤ)=G n (weakActionEnumeration (weakActionNormalization
                (WeightedCoeff.sobolevInclusion (by linarith : -1≤2*s+1) a.val)))) ∧
            ∀ a, a.val∈WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*s+1)) 1 →
              IsCompactOperator (fderiv ℂ F a+(6 : ℂ) • ContinuousLinearMap.id ℂ
                (WeightedCoeff.positiveSupportedSubmodule (Weight.sobolev (2*s+1)))) := by
  obtain ⟨V,G,hV,hCV,hG,hrec⟩ := exists_global_physical_frequency_action_corrections D
  obtain ⟨Ω,I,hΩ,hΩr,hI,hIrec,_hpos,_hzero,_hI0,_hinv⟩ := exists_global_analytic_weighted_Arnold_action_map
  refine ⟨V,G,hV,hCV,hG,global_physical_family_native_recovery D G hrec,?_⟩
  intro s hs0 hs1
  obtain ⟨U₀,F₀,hU₀,hC₀,hF₀,_hzero₀,hpair⟩ := exists_global_negativeWeighted_physical_action_packet
    D (-(2*s+1)) (s+1) (by linarith) (by linarith) (by linarith) (by ring)
  have hcomp (b : Coeff 1) (hb : b∈Coeff.nonnegativeLocus 1) :
      IsCompactOperator (fderiv ℂ (fun b => weakActionEnumeration (F₀ b)) b+
        (6 : ℂ) • ContinuousLinearMap.id ℂ (Coeff 1)) :=
    global_negativeWeighted_corrected_derivative_compact D (-(2*s+1)) (s+1)
      (by linarith) (by linarith) (by linarith) (by ring) Ω hΩr I hI hΩ hIrec
      U₀ F₀ hU₀ hC₀ hF₀ hpair b hb
  obtain ⟨U,F,hU,hCU,hF,hraw,hFc⟩ := exists_original_positive_frequency_compact (2*s+1)
    U₀ F₀ hU₀ hC₀ hF₀ hcomp
  refine ⟨U,F,hU,hCU,hF,?_,hFc⟩
  intro a ha n
  let b := (WeightedCoeff.positiveActionModelEquiv (Weight.sobolev (2*s+1)) actionIndexEquiv).symm a
  have hb : b∈Coeff.nonnegativeLocus 1 :=
    (WeightedCoeff.positiveActionModelEquiv_nonnegative _ _ a).mp ha
  have he := negativeWeighted_packet_agrees_actual_weak_frequency D (-(2*s+1)) (s+1)
    (by linarith) (by linarith) (by linarith) (by ring) U₀ F₀ hU₀ hC₀ hF₀ hpair V G hV hCV hG hrec b hb n
  simp only [neg_neg] at he
  rw [hraw a ha n,he,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]
  have hN : sobolevActionEnumeration (2*s+1) a.val=b := rfl
  rw [←hN,normalizedSobolevWeakActionInclusion_enumeration]

end NLS.Articles.KdVKdV2Frequencies
