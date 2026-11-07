import NLS.Articles.KdVPseudomeasures.OriginalHillRoughKdVFrequency

/-! Full complex local frequency identity at every real rough source.
The actual H1 identity and genuine rough finite-gap approximation also
prove that taking the real part in the global definition loses nothing. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem hillRoughKdVFrequency_complex_eq_local (P : HillProductEquationPatch)
    (D : P.MomentSeriesNeighborhood) (n : ℕ+) (q : HillRealMeanZeroSource)
    (hq : hillRealMeanZeroInclusion q ∈ D.source) :
    (hillRoughKdVFrequency n q:ℂ)=
      (2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries D.ambient n
        (hillRealMeanZeroInclusion q) := by
  obtain ⟨g,_,_,ht,hf⟩ := hillPhysicalNativeFiniteGap_approximation q
  let a := fun j : ℕ => g (fourierRealZeroTruncate (Weight.signedSobolev (-1/2)) j (hillRealSignedMap q))
  have hsource : Tendsto (fun j : ℕ => hillRealMeanZeroInclusion (a j)) atTop
      (𝓝 (hillRealMeanZeroInclusion q)) := hillRealMeanZeroInclusion.continuous.continuousAt.tendsto.comp ht
  have hleft := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((analyticAt_hillRoughKdVFrequency n q).continuousAt.tendsto.comp ht)
  have hsum := (P.analytic_centeredSecondMomentSeries D n _ hq).continuousAt.tendsto.comp hsource
  have hright : Tendsto (fun j : ℕ => (2*(Real.pi:ℂ)*(n:ℤ))^3-
      12*P.centeredSecondMomentSeries D.ambient n (hillRealMeanZeroInclusion (a j))) atTop
      (𝓝 ((2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries D.ambient n
        (hillRealMeanZeroInclusion q))) := tendsto_const_nhds.sub (tendsto_const_nhds.mul hsum)
  apply tendsto_nhds_unique_of_eventuallyEq hleft hright
  filter_upwards [hf,hsource.eventually (D.source_open.mem_nhds hq)] with j hj hjD
  obtain ⟨b,hb⟩ := hillRealFiniteGap_has_H1_representative (a j) hj.1
  have hbD : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 b) ∈ D.source := by rw [hb]; exact hjD
  have hp := hillH1_physical_frequency_eq_moment_series P D n b hbD
  have hw := hillRoughKdVFrequency_eq_physical_H1 n b
  rw [hb] at hp hw
  dsimp only [Function.comp_def]
  rw [hw]
  exact hp

end NLS.Articles.KdVPseudomeasures
