import NLS.Articles.KdVPseudomeasures.OriginalHillFrequencyMoments
import NLS.KdV.HillPrimitiveMomentAbsoluteSummability
import NLS.KdV.HillProductEquationFamilyFactory
import NLS.KdV.MiuraHillPsiOriginalEstimates

/-! Actual original rough-source weighted second moments converge
absolutely on one open complex neighborhood before every row. -/
noncomputable section
open Set NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem originalHill_exists_absolutely_summable_frequency_moments (q : HillRealMeanZeroSource) :
    ∃ P : HillProductEquationPatch, ∃ W : Set (CoeffPair 2),
    ∃ C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W,
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ hillRealMeanZeroInclusion q ∈ U ∧
      U ⊆ P.momentSource C ∧
      (∀ n m : ℕ+, ∀ d : ℕ, AnalyticOnNhd ℂ (P.centeredMoment W n m d) U) ∧
      ∀ n : ℕ+, ∀ a ∈ U,
        Summable (fun m : ℕ+ => ‖((m:ℕ):ℂ)*P.centeredMoment W n m 1 a‖) := by
  have hr : IsRealPeriodOneHminusOne (hillRealMeanZeroInclusion q) := by intro k; exact q.property k
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  obtain ⟨P,hq,_,hA⟩ := exists_hillProductEquationPatch_with_family A (hillRealMeanZeroInclusion q) hr
  have HP : SourceLemma12_12Data (by simp) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hA]; exact H
  obtain ⟨W,C,U,hU,hqU,hUC,hsum⟩ :=
    P.exists_open_centeredSecondMoment_absolute_summability HP (hillRealMeanZeroInclusion q) hq hr
  exact ⟨P,W,C,U,hU,hqU,hUC,fun n m d => (P.analytic_centeredMoment C n m d).mono hUC,hsum⟩

end NLS.Articles.KdVPseudomeasures
