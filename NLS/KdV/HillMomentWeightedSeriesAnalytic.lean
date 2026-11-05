import NLS.KdV.HillMomentWeightedSeriesBounds
import NLS.KdV.HillPrimitiveMomentSeriesAnalytic
import NLS.ZakharovShabat.SourcePeriodicGapTails

/-! The actual moment-sum sequence is Banach analytic in the literal
inverse-index weighted lp target, for every p>1, on its common source. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem analytic_positive_centeredSecondMomentSeries (P : HillProductEquationPatch)
    (D : MomentSeriesNeighborhood P) (k : ℤ) :
    AnalyticOnNhd ℂ (fun q => positiveScalarExtension
      (fun n => P.centeredSecondMomentSeries D.ambient n q) k) D.source := by
  intro a ha
  by_cases hk : k ∈ range positiveEmbedding
  · obtain ⟨n,rfl⟩ := hk
    change AnalyticAt ℂ (fun q => positiveScalarExtension
      (fun i => P.centeredSecondMomentSeries D.ambient i q) ((n:ℕ):ℤ)) a
    simpa only [positiveScalarExtension_apply] using P.analytic_centeredSecondMomentSeries D n a ha
  · simpa only [positiveScalarExtension_zero_of_not_mem_range _ k hk] using
      (analyticAt_const (v := (0:ℂ)) : AnalyticAt ℂ (fun _ : PeriodOneHminusOne => (0:ℂ)) a)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem analytic_centeredSecondMomentSequence (P : HillProductEquationPatch)
    (D : MomentSeriesNeighborhood P)
    (hfull : ∀ a ∈ D.source, ∀ n m : ℕ+,
      ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment D.ambient n m 1 a‖ ≤
        D.constant*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2*
          (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)))
    (hp : 1 < p) : AnalyticOnNhd ℂ (P.centeredSecondMomentSequence D.ambient p) D.source := by
  intro q hq
  obtain ⟨_,_,G,hG,hqG,R,hR,hgap⟩ := exists_uniform_small_sourcePeriodicGapDisplacement
    (p := 2) (by simp) (by norm_num) (P.sourcePsi q) (by norm_num : (0:ℝ) < 1)
  let T := D.source ∩ P.sourcePsi ⁻¹' G
  have hψ : AnalyticOnNhd ℂ P.sourcePsi D.source := P.analytic_sourcePsi.mono (fun a ha => (D.subset ha).1)
  have hT : IsOpen T := hψ.continuousOn.isOpen_inter_preimage D.source_open hG
  let K := (2*Real.pi*D.constant)*(1+3*‖Coeff.puncturedLattice p hp‖)
  have hC := D.constant_pos
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hA := WeightedCoeff.analytic_realization_of_bound (p := p) (Weight.signedSobolev (-1))
    (fun a => positiveScalarExtension (fun n => P.centeredSecondMomentSeries D.ambient n a)) hT
    (fun k => (P.analytic_positive_centeredSecondMomentSeries D k).mono inter_subset_left) (K*R^2) (by
      intro a ha
      obtain ⟨b,hb,hn⟩ := P.exists_weighted_centeredSecondMomentSeries D hfull hp a ha.1
      refine ⟨b,hb,hn.trans ?_⟩
      have hg := (hgap (P.sourcePsi a) ha.2).1
      have hg0 : 0 ≤ ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a)‖ := norm_nonneg _
      have hg2 : ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a)‖^2 ≤ R^2 := by nlinarith
      exact mul_le_mul_of_nonneg_left hg2 hK)
  exact hA.1 q ⟨hq,hqG⟩

end NLS.KdV.HillProductEquationPatch
