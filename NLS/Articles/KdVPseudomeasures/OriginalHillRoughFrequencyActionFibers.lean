import NLS.Articles.KdVPseudomeasures.OriginalHillRoughActionTruncation
import NLS.Articles.KdVPseudomeasures.OriginalHillRoughFrequencyExtension

/-! Genuine rough KdV frequencies are constant on ENTIRE actual native
action fibers, including all collapsed modes. Matched actual finite-gap
truncations and their genuine H1 representatives justify the rough limit. -/
noncomputable section
open Set Filter Topology NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem hillRoughKdVFrequency_eq_of_native_products (n : ℕ+)
    (p q : HillRealMeanZeroSource)
    (hp : ∀ m : ℕ+, (hillRealSignedMap p).val.val.val (m:ℤ)*(hillRealSignedMap p).val.val.val (-(m:ℤ))=
      (hillRealSignedMap q).val.val.val (m:ℤ)*(hillRealSignedMap q).val.val.val (-(m:ℤ))) :
    hillRoughKdVFrequency n p=hillRoughKdVFrequency n q := by
  have htP := (continuous_hillRoughKdVFrequency n).continuousAt.tendsto.comp
    (hillRoughFiniteGapApproximation_tendsto p)
  have htQ := (continuous_hillRoughKdVFrequency n).continuousAt.tendsto.comp
    (hillRoughFiniteGapApproximation_tendsto q)
  apply tendsto_nhds_unique_of_eventuallyEq htP htQ
  apply Filter.Eventually.of_forall
  intro N
  obtain ⟨a,ha⟩ := hillRealFiniteGap_has_H1_representative _ (hillRoughFiniteGapApproximation_mem p N)
  obtain ⟨b,hb⟩ := hillRealFiniteGap_has_H1_representative _ (hillRoughFiniteGapApproximation_mem q N)
  have hprod : ∀ m : ℕ+, ((hillIntegerSobolevEquiv 1).equiv a).val.val.val (m:ℤ)*
        ((hillIntegerSobolevEquiv 1).equiv a).val.val.val (-(m:ℤ))=
      ((hillIntegerSobolevEquiv 1).equiv b).val.val.val (m:ℤ)*
        ((hillIntegerSobolevEquiv 1).equiv b).val.val.val (-(m:ℤ)) := by
    intro m
    have hm := hillRoughFiniteGapApproximation_products p q hp N m
    rw [← ha,← hb] at hm
    simpa only [← hillIntegerSobolevEquiv_inclusion,hillIntegerTargetInclusion_apply] using hm
  dsimp only [Function.comp_def]
  rw [← ha,← hb,hillRoughKdVFrequency_eq_physical_H1,hillRoughKdVFrequency_eq_physical_H1]
  exact hillH1KdVFrequency_eq_of_products n _ _ hprod

theorem hillRoughKdVFrequency_eq_of_discriminant_eq (n : ℕ+)
    (p q : HillRealMeanZeroSource) (hp : hillRealDiscriminantData p=hillRealDiscriminantData q) :
    hillRoughKdVFrequency n p=hillRoughKdVFrequency n q :=
  hillRoughKdVFrequency_eq_of_native_products n p q
    ((hillRealDiscriminantData_eq_iff_native_products p q).mp hp)

theorem hillRoughKdVFrequency_eq_of_original_isospectral (n : ℕ+)
    (p q : HillRealMeanZeroSource)
    (hp : originalHillPotentialOfRealSource p ∈ originalIsospectralSet (originalHillPotentialOfRealSource q)) :
    hillRoughKdVFrequency n p=hillRoughKdVFrequency n q := by
  apply hillRoughKdVFrequency_eq_of_discriminant_eq n p q
  have hd := (mem_originalIsospectralSet_iff_discriminant_eq _ _).mp hp
  simpa only [← hillRealDiscriminantData_original,originalHillRealMeanZeroSource_ofRealSource] using hd

end NLS.Articles.KdVPseudomeasures
