import NLS.Articles.KdVPseudomeasures.OriginalHillH1ModeCurve
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapPhysicalFrequency
import NLS.Articles.KdVPseudomeasures.OriginalHillH1FrequencyAnalytic
import NLS.Articles.KdVPseudomeasures.OriginalHillMomentSeriesAnalytic

/-! The physical finite-gap frequency identity at ALL selected modes,
including collapsed ones, on the actual analytic moment neighborhood. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem hillH1_finiteGap_open_frequency_eq_moment_series
    (P : HillProductEquationPatch) {W : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n : ℕ+) (q : RealSignedHilbert (signedStepOrder 0 1))
    (hf : hillIntegerSourceInclusion 1 q ∈ hillRealFiniteGapLocus)
    (hq : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ P.momentSource C)
    (hn : hillHminusCanonicalGapSquare n
      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))≠0) :
    (hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q):ℂ)=
      (2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries W n
        (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) := by
  let Q := hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)
  have hr : IsRealPeriodOneHminusOne Q := (hillIntegerSourceInclusion 1 q).property
  obtain ⟨A,_,hA⟩ := exists_hillPhysicalOnIndexPhaseChart P n Q
    (P.real_mem_physicalDirichletSource Q hq.1 hr) hr hn
  exact hillH1_finiteGap_physical_frequency_eq_moment_series A C q hf hA hq

theorem hillH1_finiteGap_ALL_frequency_eq_moment_series
    (P : HillProductEquationPatch) (D : P.MomentSeriesNeighborhood)
    (n : ℕ+) (q : RealSignedHilbert (signedStepOrder 0 1))
    (hf : hillIntegerSourceInclusion 1 q ∈ hillRealFiniteGapLocus)
    (hq : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ D.source) :
    (hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q):ℂ)=
      (2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries D.ambient n
        (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) := by
  by_cases hg : hillHminusCanonicalGapSquare n
    (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))=0
  swap
  · exact hillH1_finiteGap_open_frequency_eq_moment_series P D.cauchy n q hf (D.subset hq) hg
  let L : RealSignedHilbert (signedStepOrder 0 1) →L[ℝ] PeriodOneHminusOne :=
    hillRealMeanZeroInclusion.comp (hillIntegerSourceInclusion 1)
  have ht : Tendsto (hillH1ModeCurve n 1 q) (𝓝 (0:ℝ)) (𝓝 q) := by
    simpa only [hillH1ModeCurve_zero] using (analyticAt_hillH1ModeCurve n 1 q 0).continuousAt.tendsto
  have hQ : Tendsto (fun t : ℝ => L (hillH1ModeCurve n 1 q t)) (𝓝 0) (𝓝 (L q)) :=
    L.continuous.continuousAt.tendsto.comp ht
  have hleft := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((analyticAt_hillH1KdVFrequency_actual_coordinates n q).continuousAt.tendsto.comp ht)
  have hsum := (P.analytic_centeredSecondMomentSeries D n (L q) hq).continuousAt.tendsto.comp hQ
  have hright : Tendsto (fun t : ℝ => (2*(Real.pi:ℂ)*(n:ℤ))^3-
      12*P.centeredSecondMomentSeries D.ambient n (L (hillH1ModeCurve n 1 q t))) (𝓝 0)
      (𝓝 ((2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries D.ambient n (L q))) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hsum)
  have heq : (fun t : ℝ => (hillH1KdVFrequency n
      ((hillIntegerSobolevEquiv 1).equiv (hillH1ModeCurve n 1 q t)):ℂ)) =ᶠ[𝓝[≠] (0:ℝ)]
      (fun t => (2*(Real.pi:ℂ)*(n:ℤ))^3-
        12*P.centeredSecondMomentSeries D.ambient n (L (hillH1ModeCurve n 1 q t))) := by
    filter_upwards [(hQ.eventually (D.source_open.mem_nhds hq)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t htD ht0
    exact hillH1_finiteGap_open_frequency_eq_moment_series P D.cauchy n _
      (hillH1ModeCurve_finiteGap n 1 q hf t) (D.subset htD)
      (hillH1ModeCurve_opens_closed_gap n q hg ht0)
  exact tendsto_nhds_unique_of_eventuallyEq (hleft.mono_left nhdsWithin_le_nhds)
    (hright.mono_left nhdsWithin_le_nhds) heq

end NLS.Articles.KdVPseudomeasures
