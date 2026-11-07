import NLS.Articles.KdVKdV2Frequencies.CompatibleDiagonalPairCharts
import NLS.Articles.KdVKdV2Frequencies.DiagonalGlobalFrequencyAgreement
import NLS.Articles.KdVKdV2Frequencies.DiagonalRawActionCompact
import NLS.Articles.KdVKdV2Frequencies.DiagonalActionRealizationNormalization
import NLS.Articles.KdVKdV2Frequencies.OffDiagonalRawActionCompact

/-! Combine the ACTUAL two compact action contributions on one physical
chart. The result is calibrated to the FULL global intermediate frequency
on every original nonnegative action in one original weighted ell1 germ. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem exists_corrected_frequency_compact_raw_germ
    (D : GlobalRoughAbelianForwardData) (β t : ℝ)
    (hβ : 0<β) (hβ1 : β<1) (ht : 0<t) (hβt : 2*t=1-β)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q}⊆Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω) (hΩopen : IsOpen Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (F : Coeff 1 → Coeff 1)
    (hpair : ∀ (P : NegativeWeightedFrequencyPairChart D β t) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → F (quadraticActionsExponent (q := 1) z)=P.packet z)
    (α : ℝ) (hα : -β=α) (a0 : WeightedCoeff (Weight.sobolev α) 1)
    (ha0 : a0∈WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev α) 1),
      ∃ R : WeightedCoeff (Weight.sobolev α) 1 → WeightedCoeff (Weight.sobolev α) 1,
        IsOpen U ∧ a0∈U ∧ AnalyticOnNhd ℂ R U ∧
        (∀ a∈U, IsCompactOperator (fderiv ℂ R a)) ∧
        ∀ a∈U, a∈WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1 → ∀ n : ℕ+,
          F (sobolevActionEnumeration α a) (n : ℤ)+
              6*(Weight.sobolev α (n : ℤ) : ℂ)*a.val (n : ℤ)=
            (Weight.sobolev α (n : ℤ) : ℂ)*(R a).val (n : ℤ) := by
  obtain ⟨z0,hzr,hQ,_hz2⟩ := Coeff.exists_real_quadraticActions_lift (p := 2) (q := 1)
    (by norm_num) (sobolevActionEnumeration α a0) (sobolevActionEnumeration_nonnegative α a0 ha0.1)
  obtain ⟨ε,hε,_hεβ,P,hzP,H⟩ :=
    exists_offDiagonalFrequencyPairChart_with_original_estimates D β t hβ hβ1 ht hβt z0 hzr
  obtain ⟨Q,hzQ,hQP,hR,hB⟩ := P.exists_compatible_diagonal_chart H Ω hΩ I hI hΩopen hrec z0 hzP hzr
  have hαt : 2*t-1=α := by linarith
  obtain ⟨C⟩ := Q.exists_raw_symbol_chart Ω hΩ hI hrec α hαt z0 hzQ hzr a0 hQ.symm
  obtain ⟨Gd,hGd,_hdraw,_hdzero,hdreal,hdcompact⟩ := C.exists_compact_packet
  obtain ⟨V,Go,hV,haV,hGo,_hozero,_hocenter,horeal,hocompact⟩ :=
    P.exists_raw_compact_action_germ hε α hα z0 hzP hzr a0 hQ.symm
  let U := C.domain∩V
  let R := fun a => Gd a+Go a
  have hUa : AnalyticOnNhd ℂ R U :=
    (hGd.mono inter_subset_left).add (hGo.mono inter_subset_right)
  refine ⟨U,R,C.domain_open.inter hV,⟨C.center_mem,haV⟩,hUa,?_,?_⟩
  · intro a ha
    have hd := (hGd a ha.1).differentiableAt
    have ho := (hGo a ha.2).differentiableAt
    change IsCompactOperator (fderiv ℂ (Gd+Go) a)
    rw [(hd.hasFDerivAt.add ho.hasFDerivAt).fderiv]
    exact (hdcompact a ha.1).add (hocompact a ha.2)
  · intro a ha hapos n
    obtain ⟨zd,hzd,hzdr,hi,_hs,hfactor⟩ := hdreal a ha.1 hapos
    obtain ⟨zo,hzo,hzor,hQo,hGoEq⟩ := horeal a ha.2 hapos
    have hQd := Q.normalized_actions_of_original_realization Ω hΩ hI hrec α hαt a zd hzd hzdr hi
    have hoff : P.correction n zo=Q.physicalChart.offDiagonalCorrection n (Q.roughPotential zd) := by
      rw [hR,hB]
      exact P.correction_eq_of_real_actions zd (hQP hzd) zo hzo hzdr hzor (hQo.trans hQd.symm) n
    have hgo : (Go a).val (n : ℤ)=Q.physicalChart.offDiagonalCorrection n (Q.roughPotential zd) :=
      (hGoEq n).trans hoff
    have hf := hfactor n
    rw [←hgo] at hf
    have hfreq := global_negativeWeighted_packet_diagonal_recovery D β t hβ hβ1 ht hβt F hpair Q zd hzd hzdr n
    rw [hQd,hα] at hfreq
    rw [hfreq]
    change (Weight.sobolev α (n : ℤ) : ℂ)*Q.physicalChart.correction n (Q.roughPotential zd)+
      6*(Weight.sobolev α (n : ℤ) : ℂ)*a.val (n : ℤ)=
        (Weight.sobolev α (n : ℤ) : ℂ)*((Gd a).val (n : ℤ)+(Go a).val (n : ℤ))
    linear_combination (Weight.sobolev α (n : ℤ) : ℂ)*hf

end NLS.Articles.KdVKdV2Frequencies
