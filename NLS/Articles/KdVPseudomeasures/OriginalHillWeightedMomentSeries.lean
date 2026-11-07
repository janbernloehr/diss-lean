import NLS.Articles.KdVPseudomeasures.OriginalHillMomentAllIndexBounds
import NLS.KdV.HillMomentWeightedSeriesAnalytic

/-! One common complex rough-source neighborhood supports the actual
weighted moment-sum map in EVERY lp exponent above one. This is a
spectral series; physical Hamiltonian-frequency identification is separate. -/
noncomputable section
open Set NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat NLS.LpSequence
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem originalHill_exists_analytic_weighted_moment_series (q : HillRealMeanZeroSource) :
    ∃ P : HillProductEquationPatch, ∃ D : P.MomentSeriesNeighborhood,
      hillRealMeanZeroInclusion q ∈ D.source ∧ ∀ p : ℝ≥0∞, ∀ hp : 1 < p,
        letI : Fact (1 ≤ p) := ⟨hp.le⟩
        AnalyticOnNhd ℂ (P.centeredSecondMomentSequence D.ambient p) D.source ∧
          ∀ a ∈ D.source,
            ‖P.centeredSecondMomentSequence D.ambient p a‖ ≤
              (2*Real.pi*D.constant)*(1+3*‖Coeff.puncturedLattice p hp‖)*
                ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a)‖^2 ∧
              ∀ k, (P.centeredSecondMomentSequence D.ambient p a).val k=
                positiveScalarExtension (fun n => P.centeredSecondMomentSeries D.ambient n a) k := by
  have hr : IsRealPeriodOneHminusOne (hillRealMeanZeroInclusion q) := by intro k; exact q.property k
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  obtain ⟨P,hq,_,hA⟩ := exists_hillProductEquationPatch_with_family A (hillRealMeanZeroInclusion q) hr
  have HP : SourceLemma12_12Data (by simp) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hA]; exact H
  obtain ⟨D,hD,hfull⟩ := P.exists_momentSeriesNeighborhood_all_index_bound HP (hillRealMeanZeroInclusion q) hq hr
  refine ⟨P,D,hD,?_⟩
  intro p hp
  let : Fact (1 ≤ p) := ⟨hp.le⟩
  exact ⟨P.analytic_centeredSecondMomentSequence D hfull hp,
    P.centeredSecondMomentSequence_bound_and_coefficients D hfull hp⟩

end NLS.Articles.KdVPseudomeasures
