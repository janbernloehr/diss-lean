import NLS.Articles.KdVPseudomeasures.EndpointNativeInverseRegularity
import NLS.Articles.KdVPseudomeasures.EndpointZeroFiberWeakStar
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeZeroFiber
import NLS.Topology.CompactClosureEmbedding

/-! The full original Theorem1.4 conclusion, with its corrected literal
s+1/2 target, exact original norm bounds and actual physical weak-star
topologies. Its proof below is CONDITIONAL on actual native closedness,
which remains unproved. No global theorem is asserted unconditionally. -/
noncomputable section
open Set Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- Native injectivity gives injectivity of the actual endpoint map into
the LITERAL physical real opposite-order Wiener weak dual. -/
theorem articleEndpointWeakStarCoordinates_injective_of_native_injective
    (hn : Function.Injective hillRealSignedMap) (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Function.Injective (articleEndpointWeakStarCoordinates r hr) := by
  intro p q hpq
  have he := WeightedCoeff.physicalSobolevWeakStar_injective (1/2-r) hpq
  have h := articleEndpointCoordinates_injective_of_native_injective hn r hr he
  cases p
  cases q
  congr 1

/-- The FULL inverse topology on EVERY bounded source subset follows from
native injectivity alone. The subset need not be closed. Its closure is
compact by AppendixB; no separate bounded-image or inverse premise occurs. -/
theorem isEmbedding_articleEndpointWeakStarCoordinates_on_bounded_of_native_injective
    (hn : Function.Injective hillRealSignedMap) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) :
    Topology.IsEmbedding (fun q : A => articleEndpointWeakStarCoordinates r hr q.val) := by
  exact NLS.Topology.isEmbedding_restriction_of_compact_closure
    (articleEndpointWeakStarCoordinates r hr) A
    ((isCompact_closure_source_iff_bounded r A).mpr hb)
    (continuous_articleEndpointWeakStarCoordinates_on_bounded r hr (closure A)
      ((potentialNormBounded_closure_iff r A).mpr hb))
    (articleEndpointWeakStarCoordinates_injective_of_native_injective hn r hr).injOn

/-- The actual weak-star homeomorphism onto the exact image of ANY bounded
physical subset, conditional ONLY on the remaining native injectivity. -/
def articleEndpointWeakStarHomeomorphRangeOfNativeInjective
    (hn : Function.Injective hillRealSignedMap) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) :
    A ≃ₜ range (fun q : A => articleEndpointWeakStarCoordinates r hr q.val) :=
  (isEmbedding_articleEndpointWeakStarCoordinates_on_bounded_of_native_injective hn r hr A hb).toHomeomorph

theorem articleEndpointWeakStarHomeomorphRangeOfNativeInjective_apply
    (hn : Function.Injective hillRealSignedMap) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (q : A) :
    (articleEndpointWeakStarHomeomorphRangeOfNativeInjective hn r hr A hb q).val=
      articleEndpointWeakStarCoordinates r hr q.val := rfl

/-- Precise full sourceTheorem1.4 conclusion. Parameterr=-s has0<=r<1/2.
Analyticity/local inversion use the verified original-distribution Banach
model. Boundedness uses the ORIGINAL period-two distribution norm. The
weak-star clauses use the EXACT original physical Wiener source topology
and the literal1+abs(n) target paired with its physical REAL opposite-order
Wiener predual. IsEmbedding means homeomorphism onto the exact image.
The full original Hminus-one isospectral domain and ALL multiplicities are
retained. The printed first target exponent is corrected tos+1/2. -/
structure SourceTheorem1_4Conclusion : Prop where
  bijective : ∀ (r : ℝ) (hr : AdmissiblePredualOrder r),
    Function.Bijective (articleEndpointCoordinates r hr)
  bounded : ∀ (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ),
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : Potential r, ‖q.val‖ ≤ R → ‖articleEndpointCoordinates r hr q‖ ≤ B
  analytic : ∀ (r : ℝ) (hr : AdmissiblePredualOrder r) (q : HillEndpointRealMeanZeroSource r),
    AnalyticAt ℝ (articleEndpointPhysicalMap r hr) q
  localInverse_zero : ∀ (r : ℝ) (hr : AdmissiblePredualOrder r),
    ∃ g : ArticleEndpointRealTarget r → HillEndpointRealMeanZeroSource r,
      AnalyticAt ℝ g 0 ∧ g 0=0 ∧
      (∀ᶠ q in nhds 0, g (articleEndpointPhysicalMap r hr q)=q) ∧
      (∀ᶠ z in nhds 0, articleEndpointPhysicalMap r hr (g z)=z) ∧
      fderiv ℝ g 0=(articleEndpointFreeEquiv r hr).symm.toContinuousLinearMap
  weakStar_on_every_bounded_set : ∀ (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)), PotentialNormBounded r A →
      Topology.IsEmbedding (fun q : A => articleEndpointWeakStarCoordinates r hr q.val)
  full_original_isospectral_endpoint_bound : ∀ (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : OriginalHminusOnePotential,
      P ∈ originalIsospectralSet (sourceOriginalPotential r hr q) →
      ∃ p : Potential r, sourceOriginalPotential r hr p=P ∧ ‖p.val‖ ≤ C
  weakStar_on_full_isospectral_set : ∀ (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r),
    Topology.IsEmbedding (fun p : originalIsospectralEndpointSet (sourceOriginalPotential r hr q) r =>
      articleEndpointWeakStarCoordinates r hr p.val)

/-- The exact full main statement, kept separate from its currently conditional proof. -/
def sourceTheorem1_4Statement : Prop := SourceTheorem1_4Conclusion

/-- ALL clauses of sourceTheorem1.4 follow from the SINGLE remaining actual
native closed-map obligation. That hypothesis is EXPLICIT and UNPROVED;
this theorem does not certify the main theorem as complete. -/
theorem sourceTheorem1_4_of_native_isClosedMap (hc : IsClosedMap hillRealSignedMap) :
    sourceTheorem1_4Statement := by
  have hb := hillPhysicalNative_bijective_iff_isClosedMap.mpr hc
  refine ⟨fun r hr => ⟨articleEndpointCoordinates_injective_of_native_injective hb.1 r hr,
    articleEndpointCoordinates_surjective_of_native_surjective hb.2 r hr⟩,
    sourceLemma3_6_articleNorm,analyticAt_articleEndpointPhysicalMap,articleEndpointPhysicalMap_localInverse_zero,
    isEmbedding_articleEndpointWeakStarCoordinates_on_bounded_of_native_injective hb.1,?_,?_⟩
  · intro r hr q
    obtain ⟨C,hC,hbound⟩ := sourceLemma3_5_i r hr q
    refine ⟨C,hC,fun P hP => ?_⟩
    obtain ⟨p,hp⟩ := exists_endpoint_representative_of_original_isospectral r hr q P hP
    exact ⟨p,hp,hbound p ((mem_endpointIsospectralSet_iff_original r hr q p).mpr (hp.symm ▸ hP))⟩
  · intro r hr q
    apply isEmbedding_articleEndpointWeakStarCoordinates_on_bounded_of_native_injective hb.1 r hr
    apply potentialNormBounded_originalIsospectralEndpointSet _ r hr
    rw [originalCanonicalGapValues_sourceOriginalPotential]
    exact sourceCanonicalGapValues_mem r hr q

end NLS.Articles.KdVPseudomeasures
