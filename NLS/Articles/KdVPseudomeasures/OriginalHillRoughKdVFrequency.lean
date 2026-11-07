import NLS.Articles.KdVPseudomeasures.OriginalHillMomentPatchGluing

/-! The globally defined genuine rough KdV mode frequencies. Cross-patch
moment-sum agreement makes the definition independent of all chosen local
Miura data; every mode is real analytic and agrees with the physical H1
Hamiltonian frequency on its original strong domain. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

def hillRoughFrequencyPatch (q : HillRealMeanZeroSource) : HillProductEquationPatch :=
  Classical.choose (originalHill_exists_analytic_frequency_moment_series q)

def hillRoughFrequencyNeighborhood (q : HillRealMeanZeroSource) :
    (hillRoughFrequencyPatch q).MomentSeriesNeighborhood :=
  Classical.choose (Classical.choose_spec (originalHill_exists_analytic_frequency_moment_series q))

theorem mem_hillRoughFrequencyNeighborhood (q : HillRealMeanZeroSource) :
    hillRealMeanZeroInclusion q ∈ (hillRoughFrequencyNeighborhood q).source :=
  (Classical.choose_spec (Classical.choose_spec
    (originalHill_exists_analytic_frequency_moment_series q))).1

def hillRoughKdVFrequency (n : ℕ+) (q : HillRealMeanZeroSource) : ℝ :=
  ((2*(Real.pi:ℂ)*(n:ℤ))^3-12*(hillRoughFrequencyPatch q).centeredSecondMomentSeries
    (hillRoughFrequencyNeighborhood q).ambient n (hillRealMeanZeroInclusion q)).re

theorem hillRoughKdVFrequency_eq_local (P : HillProductEquationPatch)
    (D : P.MomentSeriesNeighborhood) (n : ℕ+) (q : HillRealMeanZeroSource)
    (hq : hillRealMeanZeroInclusion q ∈ D.source) :
    hillRoughKdVFrequency n q=
      ((2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries D.ambient n
        (hillRealMeanZeroInclusion q)).re := by
  dsimp only [hillRoughKdVFrequency]
  rw [hillReal_centeredSecondMomentSeries_independent_product_patch
    (hillRoughFrequencyPatch q) P (hillRoughFrequencyNeighborhood q) D n q
    (mem_hillRoughFrequencyNeighborhood q) hq]

theorem hillRoughKdVFrequency_eq_physical_H1 (n : ℕ+)
    (q : RealSignedHilbert (signedStepOrder 0 1)) :
    hillRoughKdVFrequency n (hillIntegerSourceInclusion 1 q)=
      hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q) := by
  let a := hillIntegerSourceInclusion 1 q
  have h := hillH1_physical_frequency_eq_moment_series (hillRoughFrequencyPatch a)
    (hillRoughFrequencyNeighborhood a) n q (mem_hillRoughFrequencyNeighborhood a)
  exact (congrArg Complex.re h).symm

theorem analyticAt_hillRoughKdVFrequency (n : ℕ+) (q : HillRealMeanZeroSource) :
    AnalyticAt ℝ (hillRoughKdVFrequency n) q := by
  let P := hillRoughFrequencyPatch q
  let D := hillRoughFrequencyNeighborhood q
  have hq := mem_hillRoughFrequencyNeighborhood q
  have hL : AnalyticAt ℝ hillRealMeanZeroInclusion q :=
    @ContinuousLinearMap.analyticAt ℝ inferInstance HillRealMeanZeroSource inferInstance inferInstance
      PeriodOneHminusOne inferInstance inferInstance hillRealMeanZeroInclusion q
  have hS : AnalyticAt ℝ (fun a : HillRealMeanZeroSource =>
      P.centeredSecondMomentSeries D.ambient n (hillRealMeanZeroInclusion a)) q :=
    (P.analytic_centeredSecondMomentSeries D n _ hq).restrictScalars.comp hL
  have hC : AnalyticAt ℝ (fun a : HillRealMeanZeroSource =>
      (2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries D.ambient n
        (hillRealMeanZeroInclusion a)) q := analyticAt_const.sub (analyticAt_const.mul hS)
  have hR := (Complex.reCLM.analyticAt _).comp hC
  apply hR.congr
  filter_upwards [hillRealMeanZeroInclusion.continuous.continuousAt.preimage_mem_nhds
    (D.source_open.mem_nhds hq)] with a ha
  exact (hillRoughKdVFrequency_eq_local P D n a ha).symm

end NLS.Articles.KdVPseudomeasures
