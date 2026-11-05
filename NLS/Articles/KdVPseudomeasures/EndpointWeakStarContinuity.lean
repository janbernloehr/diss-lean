import NLS.Articles.KdVPseudomeasures.NativeEndpointBallBound
import NLS.Articles.KdVPseudomeasures.SourceWeakStarNets
import NLS.SequenceSpaces.PhysicalSignedWienerWeakStar

/-! Forward weak-star continuity for the ACTUAL original endpoint restriction.
The source retains its actual original Wiener weak-star topology. The target
uses the EXACT signed weight and opposite-order physical Wiener predual. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The ACTUAL endpoint coordinates as a functional on the ACTUAL physical
real opposite-order signed Wiener predual. -/
def originalEndpointWeakStarCoordinates (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) :
    WeakDual ℝ (WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (-(1/2-r))) 1) :=
  WeightedCoeff.physicalSignedWeakStar (1/2-r)
    (originalEndpointRealSignedCoordinates r hr q.toPotential)

/-- Bounded source weak-star convergence gives convergence of every actual
native raw coordinate, through the actual Hminus-one norm topology. -/
theorem tendsto_originalEndpoint_coordinates_of_bounded
    (r : ℝ) (hr : AdmissiblePredualOrder r) {X : Type*} {l : Filter X}
    (x : X → WeakStarPotential r) (a : WeakStarPotential r)
    (hb : PotentialNormBounded r (range x)) (hx : Tendsto x l (𝓝 a)) (n : ℤ) :
    Tendsto (fun k => (originalEndpointRealSignedCoordinates r hr (x k).toPotential).val.val.val n)
      l (𝓝 ((originalEndpointRealSignedCoordinates r hr a.toPotential).val.val.val n)) := by
  have hl := (tendsto_source_iff_lowerDistribution_of_bounded r (-1) (p := 2)
    (by norm_num) (admissible_hminusOne_threshold r hr) x a hb).mp hx
  simp only [sourceLowerDistribution_eq_potentialHminusOne r hr] at hl
  have hn : Tendsto (fun k => sourceNativePeriodOneCLM r hr (x k).toPotential.val) l
      (𝓝 (sourceNativePeriodOneCLM r hr a.toPotential.val)) :=
    periodOneOriginalExtract.continuous.continuousAt.tendsto.comp hl
  have hreal : IsRealPeriodOneHminusOne (sourceNativePeriodOneCLM r hr a.toPotential.val) := by
    rw [← originalEndpointRealSource_native r hr a.toPotential]
    exact endpointNativeInclusion_real_source r hr _
  have hm := (analyticOnNhd_hillHminusNativeComplexMap _
    (real_mem_hillHminusActionAngleNativeDomain _ hreal)).continuousAt.tendsto.comp hn
  have hc := (WeightedCoeff.evalCLM (Weight.signedSobolev (-1/2)) 2 n).continuous.continuousAt.tendsto.comp hm
  simpa only [Function.comp_def,WeightedCoeff.evalCLM_apply,
    original_endpoint_real_coordinate_matches_native] using hc

/-- Forward continuity for EVERY bounded family and EVERY filter, in the
actual physical real Wiener dual topologies, without global injectivity. -/
theorem tendsto_originalEndpointWeakStarCoordinates_of_bounded
    (r : ℝ) (hr : AdmissiblePredualOrder r) {X : Type*} {l : Filter X}
    (x : X → WeakStarPotential r) (a : WeakStarPotential r)
    (hb : PotentialNormBounded r (range x)) (hx : Tendsto x l (𝓝 a)) :
    Tendsto (fun k => originalEndpointWeakStarCoordinates r hr (x k)) l
      (𝓝 (originalEndpointWeakStarCoordinates r hr a)) := by
  apply WeightedCoeff.tendsto_physicalSignedWeakStar_of_bounded_coefficients
  · obtain ⟨R,hR⟩ := hb
    obtain ⟨B,_,hB⟩ := sourceLemma3_6 r hr R
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨B,?_⟩
    rintro _ ⟨k,rfl⟩
    exact hB _ (hR _ (mem_range_self k))
  · exact tendsto_originalEndpoint_coordinates_of_bounded r hr x a hb hx

/-- Source Lemma3.7: every original weak-star convergent SEQUENCE has
actual weak-star convergent endpoint coordinates. No boundedness premise. -/
theorem sourceLemma3_7 (r : ℝ) (hr : AdmissiblePredualOrder r)
    (x : ℕ → WeakStarPotential r) (a : WeakStarPotential r)
    (hx : Tendsto x atTop (𝓝 a)) :
    Tendsto (fun k => originalEndpointWeakStarCoordinates r hr (x k)) atTop
      (𝓝 (originalEndpointWeakStarCoordinates r hr a)) := by
  apply tendsto_originalEndpointWeakStarCoordinates_of_bounded r hr x a _ hx
  apply (potentialNormBounded_iff_coordinates r (range x)).mpr
  rw [← range_comp]
  exact WeightedCoeff.isBounded_range_of_weakStar_tendsto r _ _
    ((isClosedEmbedding_weakStarPotentialCoordinates r).continuous.continuousAt.tendsto.comp hx)

/-- The forward part of source Corollary3.8 on EVERY bounded physical subset.
This proves continuity and makes no global bijection or inverse claim. -/
theorem continuous_originalEndpointWeakStarCoordinates_on_bounded
    (r : ℝ) (hr : AdmissiblePredualOrder r) (A : Set (WeakStarPotential r))
    (hb : PotentialNormBounded r A) :
    Continuous (fun q : A => originalEndpointWeakStarCoordinates r hr q.val) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply tendsto_originalEndpointWeakStarCoordinates_of_bounded r hr Subtype.val a.val
  · obtain ⟨R,hR⟩ := hb
    exact ⟨R,fun q hq => by obtain ⟨b,rfl⟩ := hq; exact hR b.val b.property⟩
  · exact continuous_subtype_val.continuousAt.tendsto

end NLS.Articles.KdVPseudomeasures
