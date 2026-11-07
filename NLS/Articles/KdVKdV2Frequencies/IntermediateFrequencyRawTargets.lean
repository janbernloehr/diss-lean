import NLS.Articles.KdVKdV2Frequencies.NegativeWeightedWeakFrequencyCompatibility
import NLS.SequenceSpaces.WeightedAnalyticPullback
import NLS.SequenceSpaces.AnalyticLinearPacketTransport

/-! The intermediate frequency extension in the original raw weighted
action and frequency norms, with no output rescaling in its calibration. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def sobolevActionEnumeration (α : ℝ) : WeightedCoeff (Weight.sobolev α) 1 →L[ℂ] Coeff 1 :=
  weakActionEnumeration.comp (WeightedCoeff.weightIsometry (Weight.sobolev α) 1).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem sobolevActionEnumeration_apply (α : ℝ)
    (a : WeightedCoeff (Weight.sobolev α) 1) (k : ℤ) :
    sobolevActionEnumeration α a k=(Weight.sobolev α (actionIndexEquiv k : ℤ) : ℂ)*a.val (actionIndexEquiv k : ℤ) := rfl

theorem sobolevActionEnumeration_nonnegative (α : ℝ)
    (a : WeightedCoeff (Weight.sobolev α) 1) (ha : a∈WeightedCoeff.nonnegativeLocus (Weight.sobolev α) 1) :
    sobolevActionEnumeration α a∈Coeff.nonnegativeLocus 1 :=
  weakActionEnumeration_nonnegative _ ((WeightedCoeff.mem_nonnegativeLocus_iff _ _ a).mp ha)

theorem normalizedSobolevWeakActionInclusion_enumeration (α : ℝ) (hα : -1≤α)
    (a : WeightedCoeff (Weight.sobolev α) 1) :
    normalizedSobolevWeakActionInclusion α hα (sobolevActionEnumeration α a)=
      weakActionEnumeration (weakActionNormalization (WeightedCoeff.sobolevInclusion hα a)) := by
  ext k
  rw [normalizedSobolevWeakActionInclusion_apply,sobolevActionEnumeration_apply,
    mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _),weakActionEnumeration_apply]
  change (baseActionWeight k : ℂ)*a.val (actionIndexEquiv k : ℤ)=
    (Weight.sobolev (-1) (actionIndexEquiv k : ℤ) : ℂ)*
      (WeightedCoeff.sobolevInclusion hα a).val (actionIndexEquiv k : ℤ)
  rw [WeightedCoeff.sobolevInclusion_apply,baseActionWeight_eq_sobolev]

theorem exists_intermediate_raw_frequency_target
    (D : GlobalRoughAbelianForwardData) (β t : ℝ)
    (hβ : 0<β) (hβ1 : β<1) (ht : 0<t) (hβt : 2*t=1-β) (α : ℝ) (hβα : -β=α)
    (V : Set (Coeff 1)) (G : ℕ+ → Coeff 1 → ℂ)
    (hV : IsOpen V) (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n,
        G n (quadraticActionsExponent (q := 1) z)=P.correction n z) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev α) 1),
      ∃ F : WeightedCoeff (Weight.sobolev α) 1 → WeightedCoeff (Weight.sobolev α) 1,
        IsOpen U ∧ WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1⊆U ∧
        AnalyticOnNhd ℂ F U ∧
        (∀ a∈U, ∀ j : ℤ, j≤0 → (F a).val j=0) ∧
        ∀ a∈WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1, ∀ n : ℕ+,
          (F a).val (n : ℤ)=G n (weakActionEnumeration
            (weakActionNormalization (WeightedCoeff.sobolevInclusion (by rw [←hβα];linarith : -1≤α) a))) := by
  subst α
  obtain ⟨U₀,F₀,hU₀,hC₀,hF₀,hzero,hpair⟩ :=
    exists_global_negativeWeighted_physical_action_packet D β t hβ hβ1 ht hβt
  let N := sobolevActionEnumeration (-β)
  let K := (WeightedCoeff.weightIsometry (Weight.sobolev (-β)) 1).symm.toContinuousLinearEquiv.toContinuousLinearMap
  obtain ⟨U,F,hU,hC,hFa,hsub,hval⟩ := exists_analytic_linear_packet_transport N K U₀ F₀ hU₀ hF₀
    (WeightedCoeff.positiveActionLocus (Weight.sobolev (-β)) 1)
    (fun a ha => hC₀ (sobolevActionEnumeration_nonnegative _ a ha.1))
  refine ⟨U,F,hU,hC,hFa,?_,?_⟩
  · intro a ha j hj
    rw [hval a ha]
    change F₀ (N a) j/(Weight.sobolev (-β) j : ℂ)=0
    rw [hzero _ (hsub a ha) j hj,zero_div]
  · intro a ha n
    have hNa := sobolevActionEnumeration_nonnegative (-β) a ha.1
    rw [hval a (hC ha)]
    change F₀ (N a) (n : ℤ)/(Weight.sobolev (-β) (n : ℤ) : ℂ)=_
    rw [negativeWeighted_packet_agrees_actual_weak_frequency D β t hβ hβ1 ht hβt
      U₀ F₀ hU₀ hC₀ hF₀ hpair V G hV hCV hG hrec (N a) hNa n,
      mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _),
      normalizedSobolevWeakActionInclusion_enumeration]

end NLS.Articles.KdVKdV2Frequencies
