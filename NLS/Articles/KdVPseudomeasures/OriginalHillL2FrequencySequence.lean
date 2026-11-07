import NLS.Articles.KdVPseudomeasures.OriginalHillMomentAllIndexBounds
import NLS.Articles.KdVPseudomeasures.OriginalHillRoughFrequencyReality
import NLS.KdV.HillNativeL2Models
import NLS.KdV.HillL2MomentSequenceAnalytic

/-! The SAME actual original KdV frequency correction omega_n-(2*pi*n)^3
is real analytic into UNWEIGHTED ell-infinity on the entire real mean-zero
L2 source. A common complex spectral neighborhood precedes ALL indices. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.WeightedCoeff NLS.LpSequence
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

local instance : NormedSpace ℝ HillRealL2BanachSource :=
  fourierRealZeroSubmodule_normedSpace (Weight.signedSobolev 0)

private theorem source_eq (q : HillRealL2BanachSource) :
    hillRealMeanZeroInclusion (hillL2SourceInclusion q) =
      periodOneL2Inclusion (hillL2SourceCoefficients q) := by
  apply Subtype.ext
  funext k
  change (hillL2SourceInclusion q).val.val.val k = _
  rw [hillL2SourceInclusion_apply,periodOneL2Inclusion_apply,hillL2SourceCoefficients_apply]

private theorem coefficients_real (q : HillRealL2BanachSource) :
    IsRealPeriodOneHminusOne (periodOneL2Inclusion (hillL2SourceCoefficients q)) := by
  intro k
  rw [periodOneL2Inclusion_apply,periodOneL2Inclusion_apply,
    hillL2SourceCoefficients_apply,hillL2SourceCoefficients_apply]
  exact q.property k

def hillL2KdVRenormalizedFrequencySequence (q : HillRealL2BanachSource) : Coeff ⊤ :=
  Coeff.ofFunctionOrZero ⊤ (positiveScalarExtension
    (fun n => (hillRoughKdVFrequency n (hillL2SourceInclusion q):ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3))

theorem originalHill_exists_bounded_l2_frequency_neighborhood (q : HillRealL2BanachSource) :
    ∃ P : HillProductEquationPatch, ∃ D : P.MomentSeriesNeighborhood,
      ∃ U : Set (Coeff 2), IsOpen U ∧ hillL2SourceCoefficients q ∈ U ∧
        (∀ r ∈ U, periodOneL2Inclusion r ∈ D.source) ∧
        AnalyticOnNhd ℂ (P.l2CenteredSecondMomentSequence D) U ∧
        ∃ R : ℝ, 0 ≤ R ∧ ∀ r ∈ U,
          ‖P.l2CenteredSecondMomentSequence D r‖ ≤ R ∧
          ∀ k, P.l2CenteredSecondMomentSequence D r k = positiveScalarExtension
            (fun n => P.centeredSecondMomentSeries D.ambient n (periodOneL2Inclusion r)) k := by
  obtain ⟨P,D,hq,hfull,_⟩ := originalHill_exists_all_index_frequency_moment_bounds (hillL2SourceInclusion q)
  rw [source_eq] at hq
  exact ⟨P,D,P.exists_local_l2CenteredSecondMomentSequence_analytic D hfull
    (hillL2SourceCoefficients q) hq (coefficients_real q)⟩

private theorem local_coefficients (P : HillProductEquationPatch) (D : P.MomentSeriesNeighborhood)
    (q : HillRealL2BanachSource) (hq : periodOneL2Inclusion (hillL2SourceCoefficients q) ∈ D.source)
    (hc : ∀ k, P.l2CenteredSecondMomentSequence D (hillL2SourceCoefficients q) k =
      positiveScalarExtension (fun n => P.centeredSecondMomentSeries D.ambient n
        (periodOneL2Inclusion (hillL2SourceCoefficients q))) k) (k : ℤ) :
    ((-12:ℂ) • P.l2CenteredSecondMomentSequence D (hillL2SourceCoefficients q)) k =
      positiveScalarExtension (fun n => (hillRoughKdVFrequency n (hillL2SourceInclusion q):ℂ)-
        (2*(Real.pi:ℂ)*(n:ℤ))^3) k := by
  change (-12:ℂ)*P.l2CenteredSecondMomentSequence D (hillL2SourceCoefficients q) k = _
  rw [hc]
  by_cases hk : k ∈ range positiveEmbedding
  · obtain ⟨n,rfl⟩ := hk
    change (-12:ℂ)*positiveScalarExtension _ ((n:ℕ):ℤ) = positiveScalarExtension _ ((n:ℕ):ℤ)
    rw [positiveScalarExtension_apply,positiveScalarExtension_apply]
    have hqd : hillRealMeanZeroInclusion (hillL2SourceInclusion q) ∈ D.source := by rw [source_eq]; exact hq
    rw [hillRoughKdVFrequency_complex_eq_local P D n _ hqd,source_eq]
    ring
  · rw [positiveScalarExtension_zero_of_not_mem_range _ k hk,
      positiveScalarExtension_zero_of_not_mem_range _ k hk,mul_zero]

private theorem eq_local (P : HillProductEquationPatch) (D : P.MomentSeriesNeighborhood)
    (q : HillRealL2BanachSource) (hq : periodOneL2Inclusion (hillL2SourceCoefficients q) ∈ D.source)
    (hc : ∀ k, P.l2CenteredSecondMomentSequence D (hillL2SourceCoefficients q) k =
      positiveScalarExtension (fun n => P.centeredSecondMomentSeries D.ambient n
        (periodOneL2Inclusion (hillL2SourceCoefficients q))) k) :
    hillL2KdVRenormalizedFrequencySequence q =
      (-12:ℂ) • P.l2CenteredSecondMomentSequence D (hillL2SourceCoefficients q) :=
  Coeff.ofFunctionOrZero_eq_of_coordinates _ _ (local_coefficients P D q hq hc)

theorem analyticAt_hillL2KdVRenormalizedFrequencySequence (q : HillRealL2BanachSource) :
    AnalyticAt ℝ hillL2KdVRenormalizedFrequencySequence q := by
  obtain ⟨P,D,U,hU,hqU,hUD,hA,R,_,hdata⟩ := originalHill_exists_bounded_l2_frequency_neighborhood q
  have hL := @ContinuousLinearMap.analyticAt ℝ inferInstance
    HillRealL2BanachSource inferInstance inferInstance (Coeff 2) inferInstance inferInstance hillL2SourceCoefficients q
  have hS : AnalyticAt ℝ (fun a : HillRealL2BanachSource =>
      P.l2CenteredSecondMomentSequence D (hillL2SourceCoefficients a)) q :=
    (hA _ hqU).restrictScalars.comp hL
  have hC : AnalyticAt ℝ (fun a : HillRealL2BanachSource =>
      (-12:ℂ) • P.l2CenteredSecondMomentSequence D (hillL2SourceCoefficients a)) q :=
    (analyticAt_const (v := (-12:ℂ))).smul hS
  apply hC.congr
  filter_upwards [hillL2SourceCoefficients.continuous.continuousAt.preimage_mem_nhds
    (hU.mem_nhds hqU)] with a ha
  exact (eq_local P D a (hUD _ ha) (hdata _ ha).2).symm

theorem hillL2KdVRenormalizedFrequencySequence_coefficients (q : HillRealL2BanachSource) (k : ℤ) :
    hillL2KdVRenormalizedFrequencySequence q k =
      positiveScalarExtension (fun n => (hillRoughKdVFrequency n (hillL2SourceInclusion q):ℂ)-
        (2*(Real.pi:ℂ)*(n:ℤ))^3) k := by
  obtain ⟨P,D,U,_,hqU,hUD,_,R,_,hdata⟩ := originalHill_exists_bounded_l2_frequency_neighborhood q
  rw [eq_local P D q (hUD _ hqU) (hdata _ hqU).2]
  exact local_coefficients P D q (hUD _ hqU) (hdata _ hqU).2 k

theorem hillL2KdVFrequency_remainder_bound (q : HillRealL2BanachSource) (n : ℕ+) :
    ‖(hillRoughKdVFrequency n (hillL2SourceInclusion q):ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3‖ ≤
      ‖hillL2KdVRenormalizedFrequencySequence q‖ := by
  have h := lp.norm_apply_le_norm (by simp : (⊤:ℝ≥0∞) ≠ 0) (hillL2KdVRenormalizedFrequencySequence q) (n:ℤ)
  rw [hillL2KdVRenormalizedFrequencySequence_coefficients,positiveScalarExtension_apply] at h
  exact h

end NLS.Articles.KdVPseudomeasures
