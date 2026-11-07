import NLS.Articles.KdVPseudomeasures.OriginalEndpointSourceTopology

/-! Local inversion on the literal original physically real period-one
endpoint potentials, in their ORIGINAL norm topology. The inverse is
analytic as an original distribution-valued map and satisfies BOTH identities. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem exists_originalEndpointRealSignedCoordinates_localInverse
    (r : ℝ) (hr : AdmissiblePredualOrder r) :
    ∃ g : HillEndpointRealSignedTarget r → Potential r,
      AnalyticAt ℝ (fun z => (g z).val) 0 ∧ g 0=originalEndpointPotential r hr 0 ∧
      (∀ᶠ q in 𝓝 (originalEndpointPotential r hr 0), g (originalEndpointRealSignedCoordinates r hr q)=q) ∧
      (∀ᶠ z in 𝓝 (0 : HillEndpointRealSignedTarget r), originalEndpointRealSignedCoordinates r hr (g z)=z) ∧
      fderiv ℝ (fun z => (g z).val) 0=
        (originalEndpointRealInclusionCLM r hr).comp
          (WeightedCoeff.realMeanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).symm.toContinuousLinearMap := by
  obtain ⟨g,hga,hg0,hleft,hright,hdg⟩ := exists_hillEndpointRealSignedMap_localInverse r hr
  have hsource0 : originalEndpointRealSource r hr (originalEndpointPotential r hr 0)=0 :=
    originalEndpointRealSource_potential r hr 0
  have hleftOriginal : ∀ᶠ q in 𝓝 (originalEndpointPotential r hr 0),
      g (hillEndpointRealSignedMap r hr (originalEndpointRealSource r hr q))=originalEndpointRealSource r hr q := by
    have hleft0 : ∀ᶠ x in 𝓝 (originalEndpointRealSource r hr (originalEndpointPotential r hr 0)),
        g (hillEndpointRealSignedMap r hr x)=x := by simpa only [hsource0] using hleft
    exact ((continuous_originalEndpointRealSource r hr).tendsto (originalEndpointPotential r hr 0)).eventually
      (p := fun x : HillEndpointRealMeanZeroSource r => g (hillEndpointRealSignedMap r hr x)=x) hleft0
  have hIanalytic : AnalyticAt ℝ (originalEndpointRealInclusionCLM r hr) (g 0) :=
    _root_.ContinuousLinearMap.analyticAt _ _
  have hgaOriginal : AnalyticAt ℝ (fun z : HillEndpointRealSignedTarget r => originalEndpointRealInclusionCLM r hr (g z)) 0 :=
    hIanalytic.comp (f := fun z : HillEndpointRealSignedTarget r => g z) hga
  refine ⟨fun z => originalEndpointPotential r hr (g z),hgaOriginal,?_,?_,?_,?_⟩
  · change originalEndpointPotential r hr (g 0)=originalEndpointPotential r hr 0
    rw [hg0]
  · filter_upwards [hleftOriginal] with q hq
    change originalEndpointPotential r hr (g (hillEndpointRealSignedMap r hr (originalEndpointRealSource r hr q)))=q
    rw [hq,originalEndpointPotential_source]
  · filter_upwards [hright] with z hz
    change hillEndpointRealSignedMap r hr
      (originalEndpointRealSource r hr (originalEndpointPotential r hr (g z)))=z
    rw [originalEndpointRealSource_potential]
    exact hz
  · have hI : HasFDerivAt (originalEndpointRealInclusionCLM r hr) (originalEndpointRealInclusionCLM r hr) (g 0) :=
      _root_.ContinuousLinearMap.hasFDerivAt _
    have hG : HasFDerivAt g (WeightedCoeff.realMeanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).symm.toContinuousLinearMap 0 := by
      rw [← hdg]
      exact hga.differentiableAt.hasFDerivAt
    have hFinal : HasFDerivAt (fun z : HillEndpointRealSignedTarget r => originalEndpointRealInclusionCLM r hr (g z))
        ((originalEndpointRealInclusionCLM r hr).comp
          (WeightedCoeff.realMeanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).symm.toContinuousLinearMap) 0 := by
      exact @HasFDerivAt.comp ℝ inferInstance
        (HillEndpointRealSignedTarget r) inferInstance inferInstance
        (HillEndpointRealMeanZeroSource r) inferInstance inferInstance
        (FourierLebesgueSpace (2:ℝ) (-r) ⊤) inferInstance inferInstance
        g (WeightedCoeff.realMeanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).symm.toContinuousLinearMap 0
        _ _ hI hG
    exact hFinal.fderiv

end NLS.Articles.KdVPseudomeasures
