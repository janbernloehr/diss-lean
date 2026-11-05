import NLS.Articles.KdVPseudomeasures.NativeEndpointBallLocalBound
import NLS.Articles.KdVPseudomeasures.NativeEndpointBallCompactImage
import NLS.Articles.KdVPseudomeasures.OriginalEndpointRealCoordinates
import NLS.Topology.CompactLiftedLocalBound

/-! The actual endpoint Birkhoff restriction is bounded on EVERY full
physical real endpoint norm ball. A compact native real envelope gives
one complex native neighborhood before all endpoint sources and modes. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

/-- One native complex neighborhood of the entire compact real envelope
has a common actual endpoint target bound on the prescribed endpoint ball. -/
theorem exists_uniform_endpoint_ball_native_neighborhood
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ endpointRealBallNativeEnvelope r hr R ⊆ U ∧
      U ⊆ hillHminusActionAngleNativeDomain ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ q : WeightedCoeff (Weight.sobolev (-r)) ⊤, ‖q‖ ≤ R → endpointNativeInclusion r hr q ∈ U →
        ‖hillEndpointSignedMap r hr q‖ ≤ B ∧ ∀ k,
          (hillEndpointSignedMap r hr q).val k=(hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val k := by
  let X := WeightedCoeff (Weight.sobolev (-r)) ⊤
  let w := Weight.signedSobolev (1/2-r)
  let f : X × ℤ → PeriodOneHminusOne := fun p => endpointNativeInclusion r hr p.1
  let g : X × ℤ → ℝ := fun p => ‖(w p.2 : ℂ)*(hillHminusNativeComplexMap (f p)).val p.2‖
  let S : Set (X × ℤ) := {p | ‖p.1‖ ≤ R}
  obtain ⟨O,hO,hKO,B,hB,hbound⟩ := NLS.Topology.exists_open_uniform_lifted_bound
    (endpointRealBallNativeEnvelope r hr R) (isCompact_endpointRealBallNativeEnvelope r hr R) f g S (by
      intro a ha
      obtain ⟨V,hV,haV,_,C,hC,hlocal⟩ := exists_native_neighborhood_endpoint_ball_bound r hr R a
        (endpointRealBallNativeEnvelope_real r hr R a ha)
      refine ⟨V,hV,haV,C,hC,fun p hp hfp => ?_⟩
      obtain ⟨hn,hcoord⟩ := hlocal p.1 hp hfp
      change ‖(w p.2 : ℂ)*(hillHminusNativeComplexMap (endpointNativeInclusion r hr p.1)).val p.2‖ ≤ C
      rw [← hcoord p.2]
      exact (lp.norm_apply_le_norm (by simp) (WeightedCoeff.weightEquiv w ⊤
        (hillEndpointSignedMap r hr p.1)) p.2).trans hn)
  let U := O ∩ hillHminusActionAngleNativeDomain
  have hKU : endpointRealBallNativeEnvelope r hr R ⊆ U := fun a ha =>
    ⟨hKO ha,real_mem_hillHminusActionAngleNativeDomain a (endpointRealBallNativeEnvelope_real r hr R a ha)⟩
  refine ⟨U,hO.inter isOpen_hillHminusActionAngleNativeDomain,hKU,inter_subset_right,B,hB,?_⟩
  intro q hq hqU
  have hb (k : ℤ) : ‖(w k : ℂ)*(hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val k‖ ≤ B :=
    hbound (q,k) hq hqU.1
  have hm : Memℓp (fun k => (w k : ℂ)*(hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val k) ⊤ :=
    memℓp_infty ⟨B,by rintro _ ⟨k,rfl⟩; exact hb k⟩
  let z : WeightedCoeff w ⊤ := ⟨(hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val,hm⟩
  have he : hillEndpointSignedMap r hr q=z :=
    WeightedCoeff.ofFunctionOrZero_eq_of_coordinates _ _ z (fun _ => rfl)
  refine ⟨?_,fun k => ?_⟩
  · rw [he]
    change ‖WeightedCoeff.weightEquiv w ⊤ z‖ ≤ B
    exact lp.norm_le_of_forall_le hB hb
  · rw [he]

/-- The actual physical real endpoint map is bounded on every original
coefficient endpoint norm ball, including its entire infinite tails. -/
theorem exists_uniform_hillEndpointRealSignedMap_bound
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : HillEndpointRealMeanZeroSource r, ‖q‖ ≤ R →
      ‖hillEndpointRealSignedMap r hr q‖ ≤ B := by
  obtain ⟨U,_,hKU,_,B,hB,hbound⟩ := exists_uniform_endpoint_ball_native_neighborhood r hr R
  refine ⟨B,hB,fun q hq => ?_⟩
  have hb := (hbound q.val.val hq (hKU (endpointNativeInclusion_mem_realBallEnvelope r hr R q hq))).1
  change ‖(hillEndpointRealSignedMap r hr q).val.val‖ ≤ B
  rw [hillEndpointRealSignedMap_coe,hillEndpointMeanZeroMap_real_coe r hr q.val
    (endpointNativeInclusion_real_source r hr q)]
  exact hb

/-- Source Lemma3.6 for the ACTUAL original endpoint restriction: one bound
precedes every original physical potential in the prescribed norm ball. -/
theorem sourceLemma3_6 (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : Potential r, ‖q.val‖ ≤ R →
      ‖originalEndpointRealSignedCoordinates r hr q‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := exists_uniform_hillEndpointRealSignedMap_bound r hr ((2:ℝ)^r*R)
  refine ⟨B,hB,fun q hq => ?_⟩
  exact hbound (originalEndpointRealSource r hr q)
    ((norm_originalEndpointRealSource_le r hr q).trans
      (mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg (by norm_num) r)))

end NLS.Articles.KdVPseudomeasures
