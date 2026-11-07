import NLS.Articles.KdVKdV2Frequencies.GlobalCorrectedFrequencyCompact
import NLS.Articles.KdVKdV2Frequencies.NegativeWeightedWeakFrequencyCompatibility
import NLS.SequenceSpaces.WeightedPositiveActionSpace
import NLS.SequenceSpaces.CompactCorrectedDerivativeConjugate

/-! Transport the ACTUAL global frequency and its corrected derivative
back to the ORIGINAL supported positive-frequency weighted ell1 space,
with literal raw frequency values and exact original norm. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem exists_original_positive_frequency_compact
    (α : ℝ) (U : Set (Coeff 1)) (F : Coeff 1 → Coeff 1)
    (hU : IsOpen U) (hCU : Coeff.nonnegativeLocus 1⊆U) (hF : AnalyticOnNhd ℂ F U)
    (hcompact : ∀ b∈Coeff.nonnegativeLocus 1,
      IsCompactOperator (fderiv ℂ (fun b => weakActionEnumeration (F b)) b+
        (6 : ℂ) • ContinuousLinearMap.id ℂ (Coeff 1))) :
    ∃ V : Set (WeightedCoeff.positiveSupportedSubmodule (Weight.sobolev α)),
      ∃ f : WeightedCoeff.positiveSupportedSubmodule (Weight.sobolev α) →
        WeightedCoeff.positiveSupportedSubmodule (Weight.sobolev α),
        IsOpen V ∧
        {a | a.val∈WeightedCoeff.nonnegativeLocus (Weight.sobolev α) 1}⊆V ∧
        AnalyticOnNhd ℂ f V ∧
        (∀ a, a.val∈WeightedCoeff.nonnegativeLocus (Weight.sobolev α) 1 → ∀ n : ℕ+,
          (f a).val.val (n : ℤ)=
            F ((WeightedCoeff.positiveActionModelEquiv (Weight.sobolev α) actionIndexEquiv).symm a) (n : ℤ)/
              (Weight.sobolev α (n : ℤ) : ℂ)) ∧
        ∀ a, a.val∈WeightedCoeff.nonnegativeLocus (Weight.sobolev α) 1 →
          IsCompactOperator (fderiv ℂ f a+(6 : ℂ) • ContinuousLinearMap.id ℂ
            (WeightedCoeff.positiveSupportedSubmodule (Weight.sobolev α))) := by
  let L := (WeightedCoeff.positiveActionModelEquiv (Weight.sobolev α) actionIndexEquiv).toContinuousLinearEquiv
  let H := fun b => weakActionEnumeration (F b)
  have hH : AnalyticOnNhd ℂ H U := analyticOnNhd_postcompose_clm weakActionEnumeration F U hF
  have hpos (a : WeightedCoeff.positiveSupportedSubmodule (Weight.sobolev α))
      (ha : a.val∈WeightedCoeff.nonnegativeLocus (Weight.sobolev α) 1) :
      L.symm a∈Coeff.nonnegativeLocus 1 :=
    (WeightedCoeff.positiveActionModelEquiv_nonnegative _ _ a).mp ha
  obtain ⟨V,f,hV,hCV,hf,hVU,he⟩ := exists_analytic_linear_packet_transport
    L.symm.toContinuousLinearMap L.toContinuousLinearMap U H hU hH
    {a | a.val∈WeightedCoeff.nonnegativeLocus (Weight.sobolev α) 1}
    (fun a ha => hCU (hpos a ha))
  refine ⟨V,f,hV,hCV,hf,?_,?_⟩
  · intro a ha n
    rw [he a (hCV ha)]
    have h := WeightedCoeff.positiveActionModelEquiv_raw_index (Weight.sobolev α) actionIndexEquiv
      (H (L.symm a)) (actionIndexEquiv.symm n)
    simpa only [ContinuousLinearEquiv.coe_coe,H,L,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,weakActionEnumeration_apply,Equiv.apply_symm_apply] using h
  · intro a ha
    have heN : f=ᶠ[𝓝 a] (fun b => L (H (L.symm b))) := by
      filter_upwards [hV.mem_nhds (hCV ha)] with b hb
      exact he b hb
    rw [heN.fderiv_eq]
    have hc := isCompactOperator_corrected_fderiv_conjugate L H (L.symm a) 6
      (hH _ (hCU (hpos a ha))).differentiableAt (hcompact _ (hpos a ha))
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hc

end NLS.Articles.KdVKdV2Frequencies
