import NLS.Articles.KdVPseudomeasures.OriginalHillMomentAbsoluteSummability
import NLS.KdV.HillPrimitiveMomentSeriesCompactConvergence

/-! Every original real mean-zero rough source has one common complex
neighborhood before all analytic weighted moment rows and their sums.
Identification with the physical Hamiltonian frequency remains separate. -/
noncomputable section
open Set NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat
open scoped Topology
namespace NLS.Articles.KdVPseudomeasures

theorem originalHill_exists_analytic_frequency_moment_series (q : HillRealMeanZeroSource) :
    ∃ P : HillProductEquationPatch, ∃ D : P.MomentSeriesNeighborhood,
      hillRealMeanZeroInclusion q ∈ D.source ∧
      ∀ n : ℕ+,
        AnalyticOnNhd ℂ (P.centeredSecondMomentRow D.ambient n) D.source ∧
        AnalyticOnNhd ℂ (P.centeredSecondMomentSeries D.ambient n) D.source ∧
        ∀ K : Set PeriodOneHminusOne, IsCompact K → K ⊆ D.source →
          TendstoUniformlyOn (P.centeredSecondMomentPartialSum D.ambient n)
            (P.centeredSecondMomentSeries D.ambient n) Filter.atTop K := by
  have hr : IsRealPeriodOneHminusOne (hillRealMeanZeroInclusion q) := by intro k; exact q.property k
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  obtain ⟨P,hq,_,hA⟩ := exists_hillProductEquationPatch_with_family A (hillRealMeanZeroInclusion q) hr
  have HP : SourceLemma12_12Data (by simp) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hA]; exact H
  obtain ⟨D,hD⟩ := P.exists_momentSeriesNeighborhood HP (hillRealMeanZeroInclusion q) hq hr
  exact ⟨P,D,hD,fun n => ⟨P.analytic_centeredSecondMomentRow D n,
    P.analytic_centeredSecondMomentSeries D n,P.tendstoUniformlyOn_centeredSecondMomentPartialSum_of_isCompact D n⟩⟩

end NLS.Articles.KdVPseudomeasures
