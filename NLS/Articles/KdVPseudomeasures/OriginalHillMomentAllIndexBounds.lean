import NLS.Articles.KdVPseudomeasures.OriginalHillMomentSeriesAnalytic
import NLS.KdV.HillPrimitiveMomentAllIndexBound

/-! Every original real rough source has actual second-moment bounds
on one complex neighborhood BEFORE ALL row and gap indices. Analytic
series are retained on that same neighborhood. -/
noncomputable section
open Set NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem originalHill_exists_all_index_frequency_moment_bounds (q : HillRealMeanZeroSource) :
    ∃ P : HillProductEquationPatch, ∃ D : P.MomentSeriesNeighborhood,
      hillRealMeanZeroInclusion q ∈ D.source ∧
      (∀ a ∈ D.source, ∀ n m : ℕ+,
        ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment D.ambient n m 1 a‖ ≤
          D.constant*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2*
            (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) ∧
      ∀ n : ℕ+,
        AnalyticOnNhd ℂ (P.centeredSecondMomentRow D.ambient n) D.source ∧
        AnalyticOnNhd ℂ (P.centeredSecondMomentSeries D.ambient n) D.source := by
  have hr : IsRealPeriodOneHminusOne (hillRealMeanZeroInclusion q) := by intro k; exact q.property k
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  obtain ⟨P,hq,_,hA⟩ := exists_hillProductEquationPatch_with_family A (hillRealMeanZeroInclusion q) hr
  have HP : SourceLemma12_12Data (by simp) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hA]; exact H
  obtain ⟨D,hD,hbound⟩ := P.exists_momentSeriesNeighborhood_all_index_bound HP (hillRealMeanZeroInclusion q) hq hr
  exact ⟨P,D,hD,hbound,fun n => ⟨P.analytic_centeredSecondMomentRow D n,
    P.analytic_centeredSecondMomentSeries D n⟩⟩

end NLS.Articles.KdVPseudomeasures
