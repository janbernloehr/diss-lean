import NLS.Articles.KdVKdV2Frequencies.DiagonalRawActionCompact

/-! Actual action-symbol charts at EVERY original nonnegative action,
with the exact original Arnold action realization at the center. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem GlobalRoughAbelianForwardData.exists_local_diagonal_action_symbol
    (D : GlobalRoughAbelianForwardData)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q}⊆Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω) (hΩopen : IsOpen Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (t : ℝ) (ht : 0≤t) (α : ℝ) (hα : 2*t-1=α)
    (a0 : WeightedCoeff (Weight.sobolev α) 1)
    (ha0 : a0∈WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1) :
    ∃ P : DiagonalFrequencyPairChart D I t, ∃ z0 : Coeff 2 × Coeff 2,
      z0∈P.domain ∧ z0∈Coeff.realPairLocus 2 ∧
      (∀ k : ℤ, (I (P.roughPotential z0)).val k=a0.val (actionIndexEquiv k : ℤ)) ∧
      Nonempty (DiagonalActionSymbolChart P α a0 z0) := by
  obtain ⟨z0,hzr,hQ,_hz2⟩ := Coeff.exists_real_quadraticActions_lift (p := 2) (q := 1)
    (by norm_num) (sobolevActionEnumeration α a0) (sobolevActionEnumeration_nonnegative α a0 ha0.1)
  obtain ⟨P,hzP⟩ := exists_diagonalFrequencyPairChart D Ω hΩ I hI hΩopen hrec t ht z0 hzr
  refine ⟨P,z0,hzP,hzr,?_,P.exists_raw_symbol_chart Ω hΩ hI hrec α hα z0 hzP hzr a0 hQ.symm⟩
  exact fun k => P.original_actions_of_realization Ω hΩ hI hrec α hα a0 z0 hzP hzr hQ k

end NLS.Articles.KdVKdV2Frequencies
