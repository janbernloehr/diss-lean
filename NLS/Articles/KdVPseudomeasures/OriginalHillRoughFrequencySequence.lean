import NLS.Articles.KdVPseudomeasures.OriginalHillRoughFrequencyReality
import NLS.Articles.KdVPseudomeasures.OriginalHillWeightedMomentSeries

/-! The globally defined renormalized KdV frequency sequence belongs to
the literal inverse-index weighted lp space for EVERY p>1, including
infinity. It is real analytic as a map into that full Banach target. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat NLS.LpSequence
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

def hillRoughKdVRenormalizedFrequencySequence (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (q : HillRealMeanZeroSource) : WeightedCoeff (Weight.signedSobolev (-1)) p :=
  WeightedCoeff.ofFunctionOrZero (Weight.signedSobolev (-1)) p
    (positiveScalarExtension (fun n => (hillRoughKdVFrequency n q:ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3))

theorem hillRoughFrequency_local_sequence_coefficients
    (P : HillProductEquationPatch) (D : P.MomentSeriesNeighborhood)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (q : HillRealMeanZeroSource)
    (hq : hillRealMeanZeroInclusion q ∈ D.source)
    (hc : ∀ k, (P.centeredSecondMomentSequence D.ambient p (hillRealMeanZeroInclusion q)).val k=
      positiveScalarExtension (fun n => P.centeredSecondMomentSeries D.ambient n (hillRealMeanZeroInclusion q)) k)
    (k : ℤ) :
    ((-12:ℂ) • P.centeredSecondMomentSequence D.ambient p (hillRealMeanZeroInclusion q)).val k=
      positiveScalarExtension (fun n => (hillRoughKdVFrequency n q:ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3) k := by
  change (-12:ℂ)*(P.centeredSecondMomentSequence D.ambient p (hillRealMeanZeroInclusion q)).val k=_
  rw [hc]
  by_cases hk : k ∈ range positiveEmbedding
  · obtain ⟨n,rfl⟩ := hk
    change (-12:ℂ)*positiveScalarExtension _ ((n:ℕ):ℤ)=positiveScalarExtension _ ((n:ℕ):ℤ)
    rw [positiveScalarExtension_apply,positiveScalarExtension_apply,
      hillRoughKdVFrequency_complex_eq_local P D n q hq]
    ring
  · rw [positiveScalarExtension_zero_of_not_mem_range _ k hk,
      positiveScalarExtension_zero_of_not_mem_range _ k hk,mul_zero]

theorem hillRoughFrequencySequence_eq_local
    (P : HillProductEquationPatch) (D : P.MomentSeriesNeighborhood)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (q : HillRealMeanZeroSource)
    (hq : hillRealMeanZeroInclusion q ∈ D.source)
    (hc : ∀ k, (P.centeredSecondMomentSequence D.ambient p (hillRealMeanZeroInclusion q)).val k=
      positiveScalarExtension (fun n => P.centeredSecondMomentSeries D.ambient n (hillRealMeanZeroInclusion q)) k) :
    hillRoughKdVRenormalizedFrequencySequence p q=
      (-12:ℂ) • P.centeredSecondMomentSequence D.ambient p (hillRealMeanZeroInclusion q) := by
  exact WeightedCoeff.ofFunctionOrZero_eq_of_coordinates _ _ _
    (hillRoughFrequency_local_sequence_coefficients P D q hq hc)

theorem originalHill_exists_weighted_rough_frequency_neighborhood (q : HillRealMeanZeroSource) :
    ∃ P : HillProductEquationPatch, ∃ D : P.MomentSeriesNeighborhood,
      hillRealMeanZeroInclusion q ∈ D.source ∧ ∀ p : ℝ≥0∞, ∀ hp : 1 < p,
        let : Fact (1 ≤ p) := ⟨hp.le⟩
        AnalyticOnNhd ℂ (P.centeredSecondMomentSequence D.ambient p) D.source ∧
        ∀ a : HillRealMeanZeroSource, hillRealMeanZeroInclusion a ∈ D.source →
          hillRoughKdVRenormalizedFrequencySequence p a=
            (-12:ℂ) • P.centeredSecondMomentSequence D.ambient p (hillRealMeanZeroInclusion a) ∧
          ‖hillRoughKdVRenormalizedFrequencySequence p a‖ ≤
            12*((2*Real.pi*D.constant)*(1+3*‖Coeff.puncturedLattice p hp‖)*
              ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi (hillRealMeanZeroInclusion a))‖^2) ∧
          ∀ k, (hillRoughKdVRenormalizedFrequencySequence p a).val k=
            positiveScalarExtension (fun n => (hillRoughKdVFrequency n a:ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3) k := by
  obtain ⟨P,D,hq,hdata⟩ := originalHill_exists_analytic_weighted_moment_series q
  refine ⟨P,D,hq,?_⟩
  intro p hp
  let : Fact (1 ≤ p) := ⟨hp.le⟩
  obtain ⟨hA,hbound⟩ := hdata p hp
  refine ⟨hA,fun a ha => ?_⟩
  obtain ⟨hn,hc⟩ := hbound (hillRealMeanZeroInclusion a) ha
  have heq := hillRoughFrequencySequence_eq_local P D a ha hc
  refine ⟨heq,?_,?_⟩
  · rw [heq,norm_smul]
    norm_num only [norm_neg,norm_ofNat]
    exact mul_le_mul_of_nonneg_left hn (by norm_num)
  · intro k
    rw [heq]
    exact hillRoughFrequency_local_sequence_coefficients P D a ha hc k

theorem analyticAt_hillRoughKdVRenormalizedFrequencySequence
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (q : HillRealMeanZeroSource) :
    AnalyticAt ℝ (hillRoughKdVRenormalizedFrequencySequence p) q := by
  obtain ⟨P,D,hq,hdata⟩ := originalHill_exists_weighted_rough_frequency_neighborhood q
  obtain ⟨hA,hlocal⟩ := hdata p hp
  have hL : AnalyticAt ℝ hillRealMeanZeroInclusion q :=
    @ContinuousLinearMap.analyticAt ℝ inferInstance HillRealMeanZeroSource inferInstance inferInstance
      PeriodOneHminusOne inferInstance inferInstance hillRealMeanZeroInclusion q
  have hS : AnalyticAt ℝ (fun a : HillRealMeanZeroSource =>
      P.centeredSecondMomentSequence D.ambient p (hillRealMeanZeroInclusion a)) q :=
    (hA _ hq).restrictScalars.comp hL
  have hC : AnalyticAt ℝ (fun a : HillRealMeanZeroSource =>
      (-12:ℂ) • P.centeredSecondMomentSequence D.ambient p (hillRealMeanZeroInclusion a)) q :=
    (analyticAt_const (v := (-12:ℂ))).smul hS
  apply hC.congr
  filter_upwards [hillRealMeanZeroInclusion.continuous.continuousAt.preimage_mem_nhds
    (D.source_open.mem_nhds hq)] with a ha
  exact (hlocal a ha).1.symm

theorem hillRoughKdVRenormalizedFrequencySequence_coefficients
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (q : HillRealMeanZeroSource) (k : ℤ) :
    (hillRoughKdVRenormalizedFrequencySequence p q).val k=
      positiveScalarExtension (fun n => (hillRoughKdVFrequency n q:ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3) k := by
  obtain ⟨P,D,hq,hdata⟩ := originalHill_exists_weighted_rough_frequency_neighborhood q
  exact ((hdata p hp).2 q hq).2.2 k

end NLS.Articles.KdVPseudomeasures
