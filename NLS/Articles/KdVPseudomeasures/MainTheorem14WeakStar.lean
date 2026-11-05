import NLS.Articles.KdVPseudomeasures.MainTheorem14Reduction
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeInjectivity

/-! Unconditional injectivity and FULL weak-star inverse topology on
EVERY bounded original endpoint subset, including nonclosed subsets.
These are actual clauses of Theorem1.4 with its literal Wiener topologies.
The full main statement still requires native surjectivity. -/
noncomputable section
open Set Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem injective_articleEndpointWeakStarCoordinates (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Function.Injective (articleEndpointWeakStarCoordinates r hr) :=
  articleEndpointWeakStarCoordinates_injective_of_native_injective injective_hillRealSignedMap r hr

theorem isEmbedding_articleEndpointWeakStarCoordinates_on_bounded
    (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) :
    IsEmbedding (fun q : A => articleEndpointWeakStarCoordinates r hr q.val) :=
  isEmbedding_articleEndpointWeakStarCoordinates_on_bounded_of_native_injective
    injective_hillRealSignedMap r hr A hb

def articleEndpointWeakStarHomeomorphRange (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) :
    A ≃ₜ range (fun q : A => articleEndpointWeakStarCoordinates r hr q.val) :=
  (isEmbedding_articleEndpointWeakStarCoordinates_on_bounded r hr A hb).toHomeomorph

theorem articleEndpointWeakStarHomeomorphRange_apply (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (q : A) :
    (articleEndpointWeakStarHomeomorphRange r hr A hb q).val=articleEndpointWeakStarCoordinates r hr q.val := rfl

theorem isEmbedding_articleEndpointWeakStarCoordinates_on_full_isospectral_set
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    IsEmbedding (fun p : originalIsospectralEndpointSet (sourceOriginalPotential r hr q) r =>
      articleEndpointWeakStarCoordinates r hr p.val) := by
  apply isEmbedding_articleEndpointWeakStarCoordinates_on_bounded r hr
  apply potentialNormBounded_originalIsospectralEndpointSet _ r hr
  rw [originalCanonicalGapValues_sourceOriginalPotential]
  exact sourceCanonicalGapValues_mem r hr q

/-- The remaining native hypothesis is SURJECTIVITY alone. This is a
conditional proof of the FULL original main statement, not a claim that
native surjectivity or Theorem1.4 has been proved. -/
theorem sourceTheorem1_4_of_native_surjective (hs : Function.Surjective hillRealSignedMap) :
    sourceTheorem1_4Statement :=
  sourceTheorem1_4_of_native_isClosedMap
    (hillPhysicalNative_bijective_iff_isClosedMap.mp ⟨injective_hillRealSignedMap,hs⟩)

end NLS.Articles.KdVPseudomeasures
