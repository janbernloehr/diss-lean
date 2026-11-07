import NLS.Articles.KdVPseudomeasures.OriginalHillH1PhysicalFrequency
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapH1Realization

/-! The actual local moment SUMS agree across arbitrary different Miura
and product patches at every common original rough real source. Genuine
H1 physical frequency agreement and rough finite-gap density prove this;
individual cross-patch moments are not assumed identical. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem hillReal_centeredSecondMomentSeries_independent_product_patch
    (P Q : HillProductEquationPatch) (D : P.MomentSeriesNeighborhood)
    (E : Q.MomentSeriesNeighborhood) (n : ℕ+) (q : HillRealMeanZeroSource)
    (hD : hillRealMeanZeroInclusion q ∈ D.source)
    (hE : hillRealMeanZeroInclusion q ∈ E.source) :
    P.centeredSecondMomentSeries D.ambient n (hillRealMeanZeroInclusion q)=
      Q.centeredSecondMomentSeries E.ambient n (hillRealMeanZeroInclusion q) := by
  obtain ⟨g,_,_,ht,hf⟩ := hillPhysicalNativeFiniteGap_approximation q
  let a := fun j : ℕ => g (fourierRealZeroTruncate (Weight.signedSobolev (-1/2)) j (hillRealSignedMap q))
  have hsource : Tendsto (fun j : ℕ => hillRealMeanZeroInclusion (a j)) atTop
      (𝓝 (hillRealMeanZeroInclusion q)) := hillRealMeanZeroInclusion.continuous.continuousAt.tendsto.comp ht
  have hP := (P.analytic_centeredSecondMomentSeries D n _ hD).continuousAt.tendsto.comp hsource
  have hQ := (Q.analytic_centeredSecondMomentSeries E n _ hE).continuousAt.tendsto.comp hsource
  apply tendsto_nhds_unique_of_eventuallyEq hP hQ
  filter_upwards [hf,hsource.eventually (D.source_open.mem_nhds hD),
    hsource.eventually (E.source_open.mem_nhds hE)] with j hj hjD hjE
  obtain ⟨b,hb⟩ := hillRealFiniteGap_has_H1_representative (a j) hj.1
  have hbD : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 b) ∈ D.source := by rw [hb]; exact hjD
  have hbE : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 b) ∈ E.source := by rw [hb]; exact hjE
  have hp := hillH1_physical_frequency_eq_moment_series P D n b hbD
  have hq := hillH1_physical_frequency_eq_moment_series Q E n b hbE
  rw [hb] at hp hq
  dsimp only [Function.comp_def]
  linear_combination (hp-hq)/12

end NLS.Articles.KdVPseudomeasures
