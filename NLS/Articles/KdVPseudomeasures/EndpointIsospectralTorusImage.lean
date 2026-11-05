import NLS.Articles.KdVPseudomeasures.EndpointPhysicalNativeInclusions
import NLS.Articles.KdVPseudomeasures.OriginalEndpointCompactness

/-! Source Lemma3.5(i)-(ii) on the FULL original endpoint spaces.
Every original isospectral potential has the required endpoint regularity;
the actual endpoint map has exactly the entire actual endpoint action torus
as its isospectral image. No global native inverse is assumed. -/
noncomputable section
open Set NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- The entire original physical isospectral set in its endpoint realization. -/
def endpointIsospectralSet (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) : Set (Potential r) :=
  {p | sourceHillLabels r hr p=sourceHillLabels r hr q}

/-- The ordered-label realization is EXACTLY the full original physical
isospectral set, including every algebraic multiplicity. -/
theorem mem_endpointIsospectralSet_iff_original (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q p : Potential r) :
    p ∈ endpointIsospectralSet r hr q ↔
      sourceOriginalPotential r hr p ∈ originalIsospectralSet (sourceOriginalPotential r hr q) :=
  (sourceOriginalPotential_mem_isospectral_iff r r hr hr q p).symm

/-- Actual signed physical endpoint action torus, with the literal target norm. -/
def endpointActionTorus (r : ℝ) (z : HillEndpointRealSignedTarget r) : Set (HillEndpointRealSignedTarget r) :=
  {w | ∀ n : ℕ+, w.val.val.val (n:ℤ)*w.val.val.val (-(n:ℤ))=
    z.val.val.val (n:ℤ)*z.val.val.val (-(n:ℤ))}

theorem mem_endpointActionTorus_iff_native (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (z : HillEndpointRealSignedTarget r) :
    z ∈ endpointActionTorus r (originalEndpointRealSignedCoordinates r hr q) ↔
      endpointPhysicalNativeTargetInclusion r hr z ∈
        hillRealNativeActionTorus (originalHillRealMeanZeroSource (sourceOriginalPotential r hr q)) := by
  have hb := hillRealSignedMap_mem_actionTorus_of_discriminant_eq
    (originalHillRealMeanZeroSource (sourceOriginalPotential r hr q))
    (originalHillRealMeanZeroSource (sourceOriginalPotential r hr q)) rfl
  rw [← endpointPhysicalNativeTargetInclusion_originalMap r hr q] at hb
  change (∀ n : ℕ+, _=_) ↔ (∀ n : ℕ+, _=_)
  constructor
  · intro hz n
    rw [endpointPhysicalNativeTargetInclusion_apply,endpointPhysicalNativeTargetInclusion_apply]
    exact (hz n).trans (by simpa only [endpointPhysicalNativeTargetInclusion_apply] using hb n)
  · intro hz n
    have hn := hz n
    rw [endpointPhysicalNativeTargetInclusion_apply,endpointPhysicalNativeTargetInclusion_apply] at hn
    exact hn.trans (by simpa only [endpointPhysicalNativeTargetInclusion_apply] using (hb n).symm)

/-- Every member of the FULL original Hminus-one isospectral set is the
same original endpoint distribution; no endpoint-membership premise is imposed. -/
theorem exists_endpoint_representative_of_original_isospectral
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (P : OriginalHminusOnePotential)
    (hP : P ∈ originalIsospectralSet (sourceOriginalPotential r hr q)) :
    ∃ p : Potential r, sourceOriginalPotential r hr p=P := by
  have hg := sourceCanonicalGapValues_mem r hr q
  rw [← originalCanonicalGapValues_sourceOriginalPotential r hr q] at hg
  obtain ⟨p,hp⟩ := sourceTheorem2_2_ii (sourceOriginalPotential r hr q) r hr hg P hP
  refine ⟨p,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (sourceOriginalPotential_val r hr p).trans hp

/-- Source Lemma3.5(i): one ORIGINAL endpoint norm bound precedes every
member of the actual endpoint isospectral set. -/
theorem sourceLemma3_5_i (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ endpointIsospectralSet r hr q, ‖p.val‖ ≤ C := by
  have hg := sourceCanonicalGapValues_mem r hr q
  rw [← originalCanonicalGapValues_sourceOriginalPotential r hr q] at hg
  obtain ⟨C,hC⟩ := potentialNormBounded_originalIsospectralEndpointSet
    (sourceOriginalPotential r hr q) r hr hg
  refine ⟨max C 0,le_max_right _ _,fun p hp => ?_⟩
  have hmem : (⟨p⟩ : WeakStarPotential r) ∈
      originalIsospectralEndpointSet (sourceOriginalPotential r hr q) r :=
    (mem_originalIsospectralEndpointSet_iff _ r hr ⟨p⟩).mpr
      ((mem_endpointIsospectralSet_iff_original r hr q p).mp hp)
  exact (hC ⟨p⟩ hmem).trans (le_max_left _ _)


/-- Actual original isospectral endpoint inputs have exactly the required actions. -/
theorem originalEndpointMap_mem_actionTorus_of_isospectral
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q p : Potential r)
    (hp : p ∈ endpointIsospectralSet r hr q) :
    originalEndpointRealSignedCoordinates r hr p ∈
      endpointActionTorus r (originalEndpointRealSignedCoordinates r hr q) := by
  apply (mem_endpointActionTorus_iff_native r hr q _).mpr
  rw [endpointPhysicalNativeTargetInclusion_originalMap]
  apply hillRealSignedMap_mem_actionTorus_of_discriminant_eq
  rw [hillRealDiscriminantData_original,hillRealDiscriminantData_original]
  exact (mem_originalIsospectralSet_iff_discriminant_eq _ _).mp
    ((mem_endpointIsospectralSet_iff_original r hr q p).mp hp)

/-- EVERY endpoint torus point has an ACTUAL original endpoint isospectral
preimage, by native phase attainability and full original endpoint regularity. -/
theorem exists_endpoint_isospectral_preimage_of_mem_actionTorus
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (z : HillEndpointRealSignedTarget r)
    (hz : z ∈ endpointActionTorus r (originalEndpointRealSignedCoordinates r hr q)) :
    ∃ p ∈ endpointIsospectralSet r hr q, originalEndpointRealSignedCoordinates r hr p=z := by
  have hn := (mem_endpointActionTorus_iff_native r hr q z).mp hz
  obtain ⟨P,hP,hPz⟩ := original_Hill_native_isospectral_preimage (sourceOriginalPotential r hr q)
    (endpointPhysicalNativeTargetInclusion r hr z) hn
  obtain ⟨p,hp⟩ := exists_endpoint_representative_of_original_isospectral r hr q P hP
  refine ⟨p,?_,?_⟩
  · apply (mem_endpointIsospectralSet_iff_original r hr q p).mpr
    rw [hp]
    exact hP
  · apply endpointPhysicalNativeTargetInclusion_injective r hr
    rw [endpointPhysicalNativeTargetInclusion_originalMap,hp]
    exact hPz

/-- Source Lemma3.5(ii), with the full infinity endpoint and exact original
physical potential, signed weights, actions and native coordinates. -/
theorem sourceLemma3_5_ii (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    originalEndpointRealSignedCoordinates r hr '' endpointIsospectralSet r hr q=
      endpointActionTorus r (originalEndpointRealSignedCoordinates r hr q) := by
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact originalEndpointMap_mem_actionTorus_of_isospectral r hr q p hp
  · intro hz
    obtain ⟨p,hp,hpz⟩ := exists_endpoint_isospectral_preimage_of_mem_actionTorus r hr q z hz
    exact ⟨p,hp,hpz⟩

end NLS.Articles.KdVPseudomeasures
