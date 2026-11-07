import NLS.Articles.KdVPseudomeasures.OriginalHillRoughKdVFrequency
import NLS.Articles.KdVPseudomeasures.OriginalHillH1FrequencyAtZero

/-! Uniqueness and approximation characterization of the genuine rough
frequency extension, with the literal free cubic at the origin. -/
noncomputable section
open Set Filter Topology NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem continuous_hillRoughKdVFrequency (n : ℕ+) : Continuous (hillRoughKdVFrequency n) :=
  continuous_iff_continuousAt.mpr (fun q => (analyticAt_hillRoughKdVFrequency n q).continuousAt)

theorem hillRoughKdVFrequency_unique_continuous_extension (n : ℕ+)
    (f : HillRealMeanZeroSource → ℝ) (hf : Continuous f)
    (he : ∀ q : RealSignedHilbert (signedStepOrder 0 1),
      f (hillIntegerSourceInclusion 1 q)=hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q)) :
    f=hillRoughKdVFrequency n := by
  apply denseRange_hillIntegerSourceInclusion_one.equalizer hf (continuous_hillRoughKdVFrequency n)
  funext q
  exact (he q).trans (hillRoughKdVFrequency_eq_physical_H1 n q).symm

theorem hillRoughKdVFrequency_zero (n : ℕ+) :
    hillRoughKdVFrequency n 0=(2*Real.pi*(n:ℕ))^3 := by
  have h := hillRoughKdVFrequency_eq_physical_H1 n (0 : RealSignedHilbert (signedStepOrder 0 1))
  rw [map_zero,hillIntegerSobolevEquiv_zero] at h
  exact h.trans (hillH1KdVFrequency_zero n)

theorem tendsto_physical_H1_frequency_of_rough_convergence
    {ι : Type*} {l : Filter ι} (n : ℕ+) (q : HillRealMeanZeroSource)
    (a : ι → RealSignedHilbert (signedStepOrder 0 1))
    (ha : Tendsto (fun j => hillIntegerSourceInclusion 1 (a j)) l (𝓝 q)) :
    Tendsto (fun j => hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv (a j))) l
      (𝓝 (hillRoughKdVFrequency n q)) := by
  have h := (continuous_hillRoughKdVFrequency n).continuousAt.tendsto.comp ha
  simpa only [Function.comp_def,hillRoughKdVFrequency_eq_physical_H1] using h

end NLS.Articles.KdVPseudomeasures
