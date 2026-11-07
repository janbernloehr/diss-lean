import NLS.Articles.KdVPseudomeasures.OriginalHillL2FrequencySequence
import NLS.KdV.HillL2MomentLpSequence
import NLS.SequenceSpaces.FourierRealContractiveComplexification
import NLS.ComplexAnalysis.CompatibleRealBallCharts

/-! Common complex L2 frequency charts with unweighted lp remainders
for every p > 1. All charts use the same original Hill frequencies. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.WeightedCoeff NLS.LpSequence
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
local instance lemma57ChartRealL2NormedSpace : NormedSpace ℝ HillRealL2BanachSource :=
  fourierRealZeroSubmodule_normedSpace (Weight.signedSobolev 0)

abbrev HillComplexL2FrequencySource := zeroModeSubmodule (Weight.signedSobolev 0) 2

def hillComplexL2FrequencyCoefficients : HillComplexL2FrequencySource →L[ℂ] Coeff 2 :=
  (weightIsometry (Weight.signedSobolev 0) 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (zeroModeSubmodule (Weight.signedSobolev 0) 2).subtypeL

theorem hillComplexL2FrequencyCoefficients_real (q : HillRealL2BanachSource) :
    hillComplexL2FrequencyCoefficients q.val = hillL2SourceCoefficients q := rfl

theorem lemma57_source_eq (q : HillRealL2BanachSource) :
    hillRealMeanZeroInclusion (hillL2SourceInclusion q) =
      periodOneL2Inclusion (hillL2SourceCoefficients q) := by
  apply Subtype.ext
  funext k
  change (hillL2SourceInclusion q).val.val.val k = _
  rw [hillL2SourceInclusion_apply,periodOneL2Inclusion_apply,hillL2SourceCoefficients_apply]

structure L2FrequencyLpChart where
  patch : HillProductEquationPatch
  moments : patch.MomentSeriesNeighborhood
  full : patch.L2FrequencyMomentBound moments
  majorant : NLS.FunctionalAnalysis.OpenMajorantNeighborhood (Coeff 2)
    (periodOneL2Inclusion ⁻¹' moments.source) (patch.L2FrequencyHilbertMajorant)

namespace L2FrequencyLpChart

def domain (C : L2FrequencyLpChart) : Set HillComplexL2FrequencySource :=
  hillComplexL2FrequencyCoefficients ⁻¹' C.majorant.source

theorem domain_open (C : L2FrequencyLpChart) : IsOpen C.domain :=
  C.majorant.source_open.preimage
    hillComplexL2FrequencyCoefficients.continuous

def sequence (C : L2FrequencyLpChart) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (z : HillComplexL2FrequencySource) : Coeff p :=
  (-12:ℂ) • C.patch.l2CenteredSecondMomentLpSequence C.moments p (hillComplexL2FrequencyCoefficients z)

theorem lp_data (C : L2FrequencyLpChart) {p : ℝ≥0∞} [hpFact : Fact (1 ≤ p)] (hp : 1 < p) :
    AnalyticOnNhd ℂ (C.patch.l2CenteredSecondMomentLpSequence C.moments p) C.majorant.source ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ r ∈ C.majorant.source,
        ‖C.patch.l2CenteredSecondMomentLpSequence C.moments p r‖ ≤ R ∧
        ∀ k, C.patch.l2CenteredSecondMomentLpSequence C.moments p r k = positiveScalarExtension
          (fun n => C.patch.centeredSecondMomentSeries C.moments.ambient n (periodOneL2Inclusion r)) k :=
  @NLS.KdV.HillProductEquationPatch.l2MomentLp_analytic_of_majorants p hpFact hp
    C.patch C.moments C.full C.majorant.source C.majorant.source_open
    (NLS.FunctionalAnalysis.OpenMajorantNeighborhood.mapsTo_preimage
      periodOneL2Inclusion C.moments.source C.patch.L2FrequencyHilbertMajorant C.majorant)
    C.majorant.constant C.majorant.good

theorem analytic_sequence (C : L2FrequencyLpChart) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) :
    AnalyticOnNhd ℂ (C.sequence p) C.domain := by
  have h := C.lp_data hp
  intro z hz
  have ha := (h.1 _ hz).comp (hillComplexL2FrequencyCoefficients.analyticAt z)
  exact (analyticAt_const (v := (-12:ℂ))).smul ha

theorem sequence_coordinates (C : L2FrequencyLpChart) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (z : HillComplexL2FrequencySource) (hz : z ∈ C.domain) (k : ℤ) :
    C.sequence p z k = (-12:ℂ)*positiveScalarExtension
      (fun n => C.patch.centeredSecondMomentSeries C.moments.ambient n
        (periodOneL2Inclusion (hillComplexL2FrequencyCoefficients z))) k := by
  have h := C.lp_data hp
  obtain ⟨R,_,hb⟩ := h.2
  change (-12:ℂ)*C.patch.l2CenteredSecondMomentLpSequence C.moments p
    (hillComplexL2FrequencyCoefficients z) k = _
  rw [(hb _ hz).2 k]

private theorem correction_identity (w M : ℂ) : (-12:ℂ)*M=(w-12*M)-w := by ring

private theorem real_moment_coordinates (P : HillProductEquationPatch)
    (D : P.MomentSeriesNeighborhood) (a : HillRealL2BanachSource)
    (had : hillRealMeanZeroInclusion (hillL2SourceInclusion a) ∈ D.source) (k : ℤ) :
    (-12:ℂ)*positiveScalarExtension
      (fun n => P.centeredSecondMomentSeries D.ambient n
        (periodOneL2Inclusion (hillL2SourceCoefficients a))) k = positiveScalarExtension
      (fun n => (hillRoughKdVFrequency n (hillL2SourceInclusion a):ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3) k := by
  by_cases hk : k ∈ range positiveEmbedding
  · obtain ⟨n,rfl⟩ := hk
    change (-12:ℂ)*positiveScalarExtension _ ((n:ℕ):ℤ) = positiveScalarExtension _ ((n:ℕ):ℤ)
    rw [positiveScalarExtension_apply,positiveScalarExtension_apply,
      hillRoughKdVFrequency_complex_eq_local P D n (hillL2SourceInclusion a) had,lemma57_source_eq]
    exact correction_identity _ _
  · rw [positiveScalarExtension_zero_of_not_mem_range _ k hk,
      positiveScalarExtension_zero_of_not_mem_range _ k hk,mul_zero]

private theorem real_native_mem (P : HillProductEquationPatch)
    (D : P.MomentSeriesNeighborhood) (a : HillRealL2BanachSource)
    (ha : periodOneL2Inclusion (hillL2SourceCoefficients a) ∈ D.source) :
    hillRealMeanZeroInclusion (hillL2SourceInclusion a) ∈ D.source := by
  rw [lemma57_source_eq]
  exact ha

theorem sequence_real_coordinates (C : L2FrequencyLpChart) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (a : HillRealL2BanachSource) (ha : a.val ∈ C.domain) (k : ℤ) :
    C.sequence p a.val k = positiveScalarExtension
      (fun n => (hillRoughKdVFrequency n (hillL2SourceInclusion a):ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3) k := by
  have hc : hillL2SourceCoefficients a ∈ C.majorant.source := by
    rw [← hillComplexL2FrequencyCoefficients_real]
    exact ha
  have hmap := NLS.FunctionalAnalysis.OpenMajorantNeighborhood.mapsTo_preimage
    periodOneL2Inclusion C.moments.source C.patch.L2FrequencyHilbertMajorant C.majorant
  have had := real_native_mem C.patch C.moments a (hmap hc)
  calc
    _ = (-12:ℂ)*positiveScalarExtension
        (fun n => C.patch.centeredSecondMomentSeries C.moments.ambient n
          (periodOneL2Inclusion (hillComplexL2FrequencyCoefficients a.val))) k :=
      C.sequence_coordinates hp a.val ha k
    _ = (-12:ℂ)*positiveScalarExtension
        (fun n => C.patch.centeredSecondMomentSeries C.moments.ambient n
          (periodOneL2Inclusion (hillL2SourceCoefficients a))) k :=
      congrArg (fun r : Coeff 2 => (-12:ℂ)*positiveScalarExtension
        (fun n => C.patch.centeredSecondMomentSeries C.moments.ambient n (periodOneL2Inclusion r)) k)
        (hillComplexL2FrequencyCoefficients_real a)
    _ = _ := real_moment_coordinates C.patch C.moments a had k

def realSequence (p : ℝ≥0∞) (a : HillRealL2BanachSource) : Coeff p :=
  Coeff.ofFunctionOrZero p (positiveScalarExtension
    (fun n => (hillRoughKdVFrequency n (hillL2SourceInclusion a):ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3))

theorem sequence_real (C : L2FrequencyLpChart) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (a : HillRealL2BanachSource) (ha : a.val ∈ C.domain) :
    C.sequence p a.val = realSequence p a := by
  exact (Coeff.ofFunctionOrZero_eq_of_coordinates _ _ (C.sequence_real_coordinates hp a ha)).symm

end L2FrequencyLpChart

private theorem exists_chart_of_data (P : HillProductEquationPatch) (D : P.MomentSeriesNeighborhood)
    (r : Coeff 2) (hq : periodOneL2Inclusion r ∈ D.source)
    (hf : P.L2FrequencyMomentBound D) (V : Set (Coeff 2)) (hV : IsOpen V) (hrV : r ∈ V)
    (M : ℝ) (hw : ∀ a ∈ V, P.L2FrequencyHilbertMajorant a M) :
    ∃ C : L2FrequencyLpChart, r ∈ C.majorant.source := by
  have hpre := NLS.FunctionalAnalysis.mem_preimage_of_apply_mem periodOneL2Inclusion D.source r hq
  obtain ⟨A,hA⟩ := NLS.FunctionalAnalysis.exists_openMajorantNeighborhood
    (periodOneL2Inclusion ⁻¹' D.source) (D.source_open.preimage periodOneL2Inclusion.continuous)
    P.L2FrequencyHilbertMajorant r hpre V hV hrV M hw
  exact ⟨@L2FrequencyLpChart.mk P D hf A,hA⟩

theorem exists_l2FrequencyLpChart (q : HillRealL2BanachSource) : ∃ C : L2FrequencyLpChart, hillL2SourceCoefficients q ∈ C.majorant.source := by
  obtain ⟨P,D,hq,hfull,_⟩ := originalHill_exists_all_index_frequency_moment_bounds (hillL2SourceInclusion q)
  rw [lemma57_source_eq] at hq
  have hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion (hillL2SourceCoefficients q)) := by
    intro k
    rw [periodOneL2Inclusion_apply,periodOneL2Inclusion_apply,
      hillL2SourceCoefficients_apply,hillL2SourceCoefficients_apply]
    exact q.property k
  obtain ⟨V,hV,hqV,_,M,_,hw⟩ :=
    P.exists_local_l2Abelian_Hilbert_weight_majorants (hillL2SourceCoefficients q) (D.subset hq).1 hr
  have hf : P.L2FrequencyMomentBound D := by
    convert! hfull using 1
  exact exists_chart_of_data P D (hillL2SourceCoefficients q) hq hf V hV hqV M hw

end NLS.Articles.KdVPseudomeasures
