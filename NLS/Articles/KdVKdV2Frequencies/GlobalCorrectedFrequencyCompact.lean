import NLS.Articles.KdVKdV2Frequencies.CorrectedFrequencyCompactGerms
import NLS.SequenceSpaces.WeightedPositiveActionModel
import NLS.SequenceSpaces.CompactAnalyticLinearTransport

/-! Compactness of the FULL global corrected frequency derivative in
an isometric model of the ORIGINAL positive-frequency weighted ell1
space. Every boundary action and all infinite supports are included. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem global_negativeWeighted_corrected_derivative_compact
    (D : GlobalRoughAbelianForwardData) (β t : ℝ)
    (hβ : 0<β) (hβ1 : β<1) (ht : 0<t) (hβt : 2*t=1-β)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q}⊆Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω) (hΩopen : IsOpen Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (U : Set (Coeff 1)) (F : Coeff 1 → Coeff 1)
    (hU : IsOpen U) (hCU : Coeff.nonnegativeLocus 1⊆U) (hF : AnalyticOnNhd ℂ F U)
    (hpair : ∀ (P : NegativeWeightedFrequencyPairChart D β t) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → F (quadraticActionsExponent (q := 1) z)=P.packet z)
    (b0 : Coeff 1) (hb0 : b0∈Coeff.nonnegativeLocus 1) :
    IsCompactOperator (fderiv ℂ (fun b => weakActionEnumeration (F b)) b0+
      (6 : ℂ) • ContinuousLinearMap.id ℂ (Coeff 1)) := by
  let w := Weight.sobolev (-β)
  let J := (WeightedCoeff.positiveActionLift w actionIndexEquiv).toContinuousLinearMap
  let K := WeightedCoeff.positiveActionRestriction w actionIndexEquiv
  have hJpos (b : Coeff 1) (hb : b∈Coeff.nonnegativeLocus 1) :
      J b∈WeightedCoeff.positiveActionLocus w 1 :=
    WeightedCoeff.positiveActionLift_mem_positiveActionLocus w actionIndexEquiv b hb
  have hNJ (b : Coeff 1) : sobolevActionEnumeration (-β) (J b)=b :=
    WeightedCoeff.positiveActionRestriction_lift w actionIndexEquiv b
  obtain ⟨T,R,hT,haT,hR,hRc,hcal⟩ := exists_corrected_frequency_compact_raw_germ
    D β t hβ hβ1 ht hβt Ω hΩ I hI hΩopen hrec F hpair (-β) rfl (J b0) (hJpos b0 hb0)
  obtain ⟨V,H,hV,hbV,hH,hVT,hval,hHc⟩ := exists_analytic_compact_linear_transport J K T R hT hR hRc b0 haT
  let W := V∩U
  have hW : IsOpen W := hV.inter hU
  have hf : AnalyticOnNhd ℂ (fun b => weakActionEnumeration (F b)) U :=
    analyticOnNhd_postcompose_clm weakActionEnumeration F U hF
  apply Coeff.isCompactOperator_corrected_fderiv_of_local_cone_calibration U W hW inter_subset_right
    (fun b => weakActionEnumeration (F b)) H hf (hH.mono inter_subset_left) 6 b0 ⟨hbV,hCU hb0⟩ hb0 (hHc b0 hbV)
  intro b hb hbpos
  rw [hval b hb.1]
  ext k
  have hh := hcal (J b) (hVT b hb.1) (hJpos b hbpos) (actionIndexEquiv k)
  rw [hNJ] at hh
  have hnorm : (w (actionIndexEquiv k : ℤ) : ℂ)*(J b).val (actionIndexEquiv k : ℤ)=b k := by
    exact congrArg (fun x : Coeff 1 => x k) (hNJ b)
  change F b (actionIndexEquiv k : ℤ)+6*b k=
    (w (actionIndexEquiv k : ℤ) : ℂ)*(R (J b)).val (actionIndexEquiv k : ℤ)
  change F b (actionIndexEquiv k : ℤ)+6*(w (actionIndexEquiv k : ℤ) : ℂ)*(J b).val (actionIndexEquiv k : ℤ)=
    (w (actionIndexEquiv k : ℤ) : ℂ)*(R (J b)).val (actionIndexEquiv k : ℤ) at hh
  rw [mul_assoc,hnorm] at hh
  exact hh

end NLS.Articles.KdVKdV2Frequencies
