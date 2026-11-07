import NLS.Articles.KdVKdV2Frequencies.DiagonalFrequencyPairCharts
import NLS.Articles.KdVKdV2Frequencies.WeightedPairArnoldActions
import NLS.Articles.KdVKdV2Frequencies.IntermediateFrequencyRawTargets

/-! Real pair realizations in the diagonal action charts have the
ORIGINAL intrinsic Arnold actions, coefficient for coefficient. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.DiagonalFrequencyPairChart

theorem original_actions_of_realization
    {D : GlobalRoughAbelianForwardData} {I : PeriodOneHminusOne → BaseActionSpace} {t : ℝ}
    (P : DiagonalFrequencyPairChart D I t)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q}⊆Ω)
    (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (α : ℝ) (hα : 2*t-1=α) (a : WeightedCoeff (Weight.sobolev α) 1)
    (z : Coeff 2 × Coeff 2) (hz : z∈P.domain) (hzr : z∈Coeff.realPairLocus 2)
    (hQ : quadraticActionsExponent (q := 1) z=sobolevActionEnumeration α a) (k : ℤ) :
    (I (P.roughPotential z)).val k=a.val (actionIndexEquiv k : ℤ) := by
  have h := Arnold_action_of_weighted_pair_inverse_identity D Ω hΩ I hI hrec t
    (P.roughPotential z) (P.rough_real z hz hzr) z hzr (P.rough_signed z hz hzr) k
  rw [hα,hQ,sobolevActionEnumeration_apply] at h
  exact mul_left_cancel₀ (Weight.complex_ne_zero _ _) h

end NLS.Articles.KdVKdV2Frequencies.DiagonalFrequencyPairChart
