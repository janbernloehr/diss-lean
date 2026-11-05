import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapClosedFrequency
import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerFiniteGapApproximation

/-! The actual physical H1 KdV frequency equals its exact local moment
series at EVERY H1 source and EVERY mode, including collapsed modes.
The same local moment neighborhood is retained throughout approximation. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem hillH1_physical_frequency_eq_moment_series
    (P : HillProductEquationPatch) (D : P.MomentSeriesNeighborhood)
    (n : ℕ+) (q : RealSignedHilbert (signedStepOrder 0 1))
    (hq : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ D.source) :
    (hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q):ℂ)=
      (2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries D.ambient n
        (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) := by
  let L : RealSignedHilbert (signedStepOrder 0 1) →L[ℝ] PeriodOneHminusOne :=
    hillRealMeanZeroInclusion.comp (hillIntegerSourceInclusion 1)
  have ht := hillIntegerFiniteGapApproximation_tendsto 1 q
  have hQ : Tendsto (fun j : ℕ => L (hillIntegerFiniteGapApproximation 1 q j)) atTop (𝓝 (L q)) :=
    L.continuous.continuousAt.tendsto.comp ht
  have hleft := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((analyticAt_hillH1KdVFrequency_actual_coordinates n q).continuousAt.tendsto.comp ht)
  have hsum := (P.analytic_centeredSecondMomentSeries D n (L q) hq).continuousAt.tendsto.comp hQ
  have hright : Tendsto (fun j : ℕ => (2*(Real.pi:ℂ)*(n:ℤ))^3-
      12*P.centeredSecondMomentSeries D.ambient n (L (hillIntegerFiniteGapApproximation 1 q j))) atTop
      (𝓝 ((2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries D.ambient n (L q))) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hsum)
  have heq : (fun j : ℕ => (hillH1KdVFrequency n
      ((hillIntegerSobolevEquiv 1).equiv (hillIntegerFiniteGapApproximation 1 q j)):ℂ)) =ᶠ[atTop]
      (fun j => (2*(Real.pi:ℂ)*(n:ℤ))^3-
        12*P.centeredSecondMomentSeries D.ambient n (L (hillIntegerFiniteGapApproximation 1 q j))) := by
    filter_upwards [hQ.eventually (D.source_open.mem_nhds hq)] with j hj
    exact hillH1_finiteGap_ALL_frequency_eq_moment_series P D n _
      (hillIntegerFiniteGapApproximation_mem 1 q j) hj
  exact tendsto_nhds_unique_of_eventuallyEq hleft hright heq

theorem originalHill_exists_physical_H1_frequency_moment_neighborhood (q : HillRealMeanZeroSource) :
    ∃ P : HillProductEquationPatch, ∃ D : P.MomentSeriesNeighborhood,
      hillRealMeanZeroInclusion q ∈ D.source ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (P.centeredSecondMomentSeries D.ambient n) D.source) ∧
      ∀ a : RealSignedHilbert (signedStepOrder 0 1),
        hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 a) ∈ D.source →
        ∀ n : ℕ+, (hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv a):ℂ)=
          (2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries D.ambient n
            (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 a)) := by
  obtain ⟨P,D,hq,ha⟩ := originalHill_exists_analytic_frequency_moment_series q
  exact ⟨P,D,hq,fun n => (ha n).2.1,fun a ha n =>
    hillH1_physical_frequency_eq_moment_series P D n a ha⟩

end NLS.Articles.KdVPseudomeasures
