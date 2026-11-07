import NLS.Articles.KdVPseudomeasures.SourceNoncompactTori
import NLS.Articles.KdVPseudomeasures.SourceFrequencyDivergence
import NLS.Articles.KdVPseudomeasures.OriginalHillEndpointCanonicalFlow
import NLS.SequenceSpaces.FourierRealPhaseNoncontinuity

/-! Strong norm discontinuity of the same actual endpoint KdV flow at
all inputs whose literal target-order weighted tails do not vanish. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem articleEndpointCoordinates_native_coefficient (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (k : ℤ) :
    (articleEndpointCoordinates r hr q).val.val.val k=
      (hillRealSignedMap (originalHillRealMeanZeroSource (sourceOriginalPotential r hr q))).val.val.val k := by
  rw [articleEndpointCoordinates,articleEndpointTargetEquiv_apply,
    ← endpointPhysicalNativeTargetInclusion_originalMap r hr q,endpointPhysicalNativeTargetInclusion_apply]

theorem articleEndpointCoordinates_flow_positive (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (t : ℝ) (n : ℕ+) :
    (articleEndpointCoordinates r hr (hillEndpointCanonicalKdVFlow r hr q t)).val.val.val (n:ℤ)=
      Complex.exp (((t*hillRoughKdVFrequency n
        (originalHillRealMeanZeroSource (sourceOriginalPotential r hr q)):ℝ):ℂ)*Complex.I)*
          (articleEndpointCoordinates r hr q).val.val.val (n:ℤ) := by
  rw [articleEndpointCoordinates_native_coefficient,hillEndpointCanonicalKdVFlow_original,
    hillOriginalCanonicalKdVFlow,originalHillRealMeanZeroSource_ofRealSource,
    hillRoughCanonicalKdVFlow_positive_coordinate,articleEndpointCoordinates_native_coefficient]

theorem sourceKdV_not_continuousAt_norm_of_not_c0 (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r)
    (hq : ¬PositiveWeightedC0 (Weight.sobolev (1/2-r)) (articleEndpointCoordinates r hr q)) :
    ¬ContinuousAt (hillEndpointCanonicalKdVFlow r hr q) 0 := by
  intro hc
  have hF : Continuous (articleEndpointCoordinates r hr) :=
    (articleEndpointTargetEquiv r hr).continuous.comp (continuous_originalEndpointRealSignedCoordinates r hr)
  have hcurve : ContinuousAt (fun t => articleEndpointCoordinates r hr (hillEndpointCanonicalKdVFlow r hr q t)) 0 :=
    hF.continuousAt.comp hc
  apply hq
  apply positiveWeightedC0_of_continuous_positive_phases (Weight.sobolev (1/2-r))
    (articleEndpointCoordinates r hr q)
    (fun t => articleEndpointCoordinates r hr (hillEndpointCanonicalKdVFlow r hr q t))
    (by rw [hillEndpointCanonicalKdVFlow_zero])
    (fun j => hillRoughKdVFrequency ⟨j+1,Nat.succ_pos j⟩
      (originalHillRealMeanZeroSource (sourceOriginalPotential r hr q)))
    (hillRoughKdVFrequency_tendsto_atTop _) _ hcurve
  intro t j
  exact articleEndpointCoordinates_flow_positive r hr q t ⟨j+1,Nat.succ_pos j⟩

/-- An explicit endpoint example for each order, obtained from the actual
inverse of the non-c0 real target. -/
theorem exists_sourceKdV_not_continuousAt_norm (r : ℝ) (hr : AdmissiblePredualOrder r) :
    ∃ q : Potential r, ¬ContinuousAt (hillEndpointCanonicalKdVFlow r hr q) 0 := by
  let z : ArticleEndpointRealTarget r := realInverseWeightCoefficients (Weight.sobolev (1/2-r))
    (Weight.sobolev_neg (1/2-r))
  obtain ⟨q,hq⟩ := (sourceTheorem1_4.bijective r hr).2 z
  refine ⟨q,sourceKdV_not_continuousAt_norm_of_not_c0 r hr q ?_⟩
  rw [hq]
  exact not_positiveWeightedC0_realInverseWeightCoefficients _ _

end NLS.Articles.KdVPseudomeasures
