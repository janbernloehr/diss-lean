import NLS.Articles.KdVPseudomeasures.ArticleEndpointTargetNorm
import NLS.Articles.KdVPseudomeasures.EndpointWeakStarContinuity
import NLS.SequenceSpaces.PhysicalSobolevWienerWeakStar

/-! Actual forward endpoint weak-star continuity with the article's LITERAL
1+abs(n) target weight and the EXACT opposite-order physical Wiener predual.
The native signed norm is connected by a proved coefficient-preserving
Banach equivalence, not silently identified with the article norm. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

def articleEndpointWeakStarCoordinates (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) :
    WeakDual ℝ (WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (-(1/2-r))) 1) :=
  WeightedCoeff.physicalSobolevWeakStar (1/2-r) (articleEndpointCoordinates r hr q.toPotential)

/-- Forward convergence along EVERY bounded original source family and EVERY
filter, with the article's literal target pairing and opposite-order predual. -/
theorem tendsto_articleEndpointWeakStarCoordinates_of_bounded
    (r : ℝ) (hr : AdmissiblePredualOrder r) {X : Type*} {l : Filter X}
    (x : X → WeakStarPotential r) (a : WeakStarPotential r)
    (hb : PotentialNormBounded r (range x)) (hx : Tendsto x l (𝓝 a)) :
    Tendsto (fun k => articleEndpointWeakStarCoordinates r hr (x k)) l
      (𝓝 (articleEndpointWeakStarCoordinates r hr a)) := by
  apply WeightedCoeff.tendsto_physicalSobolevWeakStar_of_bounded_coefficients
  · obtain ⟨R,hR⟩ := hb
    obtain ⟨B,_,hB⟩ := sourceLemma3_6_articleNorm r hr R
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨B,?_⟩
    rintro _ ⟨k,rfl⟩
    exact hB _ (hR _ (mem_range_self k))
  · intro n
    simpa only [articleEndpointCoordinates,articleEndpointTargetEquiv_apply] using
      tendsto_originalEndpoint_coordinates_of_bounded r hr x a hb hx n

/-- Full source Lemma3.7 with the article's LITERAL target topology.
No additional boundedness hypothesis is imposed on convergent sequences. -/
theorem sourceLemma3_7_articleNorm (r : ℝ) (hr : AdmissiblePredualOrder r)
    (x : ℕ → WeakStarPotential r) (a : WeakStarPotential r)
    (hx : Tendsto x atTop (𝓝 a)) :
    Tendsto (fun k => articleEndpointWeakStarCoordinates r hr (x k)) atTop
      (𝓝 (articleEndpointWeakStarCoordinates r hr a)) := by
  apply tendsto_articleEndpointWeakStarCoordinates_of_bounded r hr x a _ hx
  apply (potentialNormBounded_iff_coordinates r (range x)).mpr
  rw [← range_comp]
  exact WeightedCoeff.isBounded_range_of_weakStar_tendsto r _ _
    ((isClosedEmbedding_weakStarPotentialCoordinates r).continuous.continuousAt.tendsto.comp hx)

/-- The FORWARD continuity part of source Corollary3.8 on EVERY original
bounded subset, with the article's literal Wiener weak-star topologies. -/
theorem continuous_articleEndpointWeakStarCoordinates_on_bounded
    (r : ℝ) (hr : AdmissiblePredualOrder r) (A : Set (WeakStarPotential r))
    (hb : PotentialNormBounded r A) :
    Continuous (fun q : A => articleEndpointWeakStarCoordinates r hr q.val) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply tendsto_articleEndpointWeakStarCoordinates_of_bounded r hr Subtype.val a.val
  · obtain ⟨R,hR⟩ := hb
    exact ⟨R,fun q hq => by obtain ⟨b,rfl⟩ := hq; exact hR b.val b.property⟩
  · exact continuous_subtype_val.continuousAt.tendsto

end NLS.Articles.KdVPseudomeasures
