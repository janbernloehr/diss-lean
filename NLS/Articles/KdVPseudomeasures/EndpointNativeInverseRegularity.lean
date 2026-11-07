import NLS.Articles.KdVPseudomeasures.ArticleEndpointTargetNorm
import NLS.Articles.KdVPseudomeasures.OriginalEndpointMembership
import NLS.KdV.HillNativeInverseGapTail
import NLS.SequenceSpaces.FiniteTailDomination

/-! Endpoint regularity of an ACTUAL native output forces endpoint
regularity of its SAME original potential. Native surjectivity and
injectivity are explicit remaining premises in the transfer theorems. -/
noncomputable section
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- An actual native preimage of an endpoint output has the required
actual ORIGINAL gap regularity, including every finite low cluster. -/
theorem originalCanonicalGaps_mem_of_native_endpoint_output
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : OriginalHminusOnePotential)
    (z : HillEndpointRealSignedTarget r)
    (hz : hillRealSignedMap (originalHillRealMeanZeroSource q)=endpointPhysicalNativeTargetInclusion r hr z) :
    Memℓp (fun k : ℤ => (Weight.sobolev (-r) k:ℂ)*originalCanonicalGapValues q k) ⊤ := by
  let a := (WeightedCoeff.realMeanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).symm z
  have ha := a.val.val.property
  change Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*a.val.val.val k) ⊤ at ha
  obtain ⟨N,hN,hbound⟩ := exists_hillReal_native_inverse_gap_tail (originalHillRealMeanZeroSource q)
  apply NLS.memlp_of_natAbs_tail_norm_le _ _ ha N 3 (by norm_num)
  intro k hk
  have hk0 : k ≠ 0 := by intro h; subst k; simp only [Int.natAbs_zero] at hk; omega
  have he : ((WeightedCoeff.realMeanZeroHalfFourierEquiv 2).symm
      (hillRealSignedMap (originalHillRealMeanZeroSource q))).val.val.val k=a.val.val.val k := by
    rw [WeightedCoeff.realMeanZeroHalfFourierEquiv_symm_apply,hz,
      endpointPhysicalNativeTargetInclusion_apply,WeightedCoeff.realMeanZeroNegativeOrderHalfFourierEquiv_symm_apply]
  have hg : ‖originalCanonicalGapValues q k‖ ≤ 3*‖a.val.val.val k‖ := by
    have h := hbound k hk
    rw [he] at h
    change ‖((hillHminusLabels (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)
      (2*k.natAbs)-hillHminusLabels (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)
      (2*k.natAbs-1):ℝ):ℂ)‖ ≤ 3*‖a.val.val.val k‖ at h
    simpa only [originalCanonicalGapValues,if_neg hk0,originalHillLabels] using h
  calc
    _=‖(Weight.sobolev (-r) k:ℂ)‖*‖originalCanonicalGapValues q k‖ := norm_mul _ _
    _≤‖(Weight.sobolev (-r) k:ℂ)‖*(3*‖a.val.val.val k‖) :=
      mul_le_mul_of_nonneg_left hg (norm_nonneg _)
    _=3*‖(Weight.sobolev (-r) k:ℂ)*a.val.val.val k‖ := by rw [norm_mul]; ring

/-- The SAME native preimage is an original endpoint potential, with the
EXACT supplied endpoint output; no inverse-map or injectivity premise is used. -/
theorem exists_endpoint_preimage_of_native_endpoint_output
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : OriginalHminusOnePotential)
    (z : HillEndpointRealSignedTarget r)
    (hz : hillRealSignedMap (originalHillRealMeanZeroSource q)=endpointPhysicalNativeTargetInclusion r hr z) :
    ∃ p : Potential r, sourceOriginalPotential r hr p=q ∧ originalEndpointRealSignedCoordinates r hr p=z := by
  obtain ⟨p,hp⟩ := sourceTheorem2_2_i q r hr
    (originalCanonicalGaps_mem_of_native_endpoint_output r hr q z hz)
  have ho : sourceOriginalPotential r hr p=q := by
    apply Subtype.ext
    apply Subtype.ext
    exact (sourceOriginalPotential_val r hr p).trans hp
  refine ⟨p,ho,?_⟩
  apply endpointPhysicalNativeTargetInclusion_injective r hr
  rw [endpointPhysicalNativeTargetInclusion_originalMap,ho]
  exact hz

/-- Native onto-ness alone supplies the ACTUAL full endpoint onto-ness.
Endpoint regularity of the recovered input is proved, not assumed. -/
theorem articleEndpointCoordinates_surjective_of_native_surjective
    (hn : Function.Surjective hillRealSignedMap) (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Function.Surjective (articleEndpointCoordinates r hr) := by
  intro z
  let w := (articleEndpointTargetEquiv r hr).symm z
  obtain ⟨q,hq⟩ := hn (endpointPhysicalNativeTargetInclusion r hr w)
  obtain ⟨p,_,hp⟩ := exists_endpoint_preimage_of_native_endpoint_output r hr
    (originalHillPotentialOfRealSource q) w (by rw [originalHillRealMeanZeroSource_ofRealSource]; exact hq)
  refine ⟨p,?_⟩
  change articleEndpointTargetEquiv r hr (originalEndpointRealSignedCoordinates r hr p)=z
  rw [hp]
  exact (articleEndpointTargetEquiv r hr).apply_symm_apply z

/-- Native injectivity transfers to the actual restriction on ENTIRE
original endpoint distributions. The native premise is not asserted proved. -/
theorem articleEndpointCoordinates_injective_of_native_injective
    (hn : Function.Injective hillRealSignedMap) (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Function.Injective (articleEndpointCoordinates r hr) := by
  intro p q hpq
  have he := (articleEndpointTargetEquiv r hr).injective hpq
  have h := congrArg (endpointPhysicalNativeTargetInclusion r hr) he
  rw [endpointPhysicalNativeTargetInclusion_originalMap,endpointPhysicalNativeTargetInclusion_originalMap] at h
  have hs := congrArg hillRealMeanZeroInclusion (hn h)
  rw [originalHillRealMeanZeroSource_inclusion,originalHillRealMeanZeroSource_inclusion] at hs
  have hd := congrArg periodOneOriginal hs
  rw [periodOneOriginal_originalPeriodOneCoefficients,periodOneOriginal_originalPeriodOneCoefficients] at hd
  apply Subtype.ext
  apply Subtype.ext
  exact (sourceOriginalPotential_val r hr p).symm.trans
    ((congrArg Subtype.val hd).trans (sourceOriginalPotential_val r hr q))

end NLS.Articles.KdVPseudomeasures
