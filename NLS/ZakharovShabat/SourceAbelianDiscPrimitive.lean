import NLS.ComplexAnalysis.PrimitiveOnDiscComplement
import NLS.ComplexAnalysis.SegmentIsolatingCircles
import NLS.ComplexAnalysis.SegmentPrimitiveBoundary
import NLS.ZakharovShabat.SourceCriticalRootRatioCircleAllGaps
import NLS.ZakharovShabat.SourceCriticalRootRatioNestedCircle
import NLS.ZakharovShabat.SourceCriticalRootRatioEndpointPuncturedBound

/-! # Abelian primitives on isolating discs minus the selected gap

Vanishing of the actual quotient's enclosing-circle period removes the
obstruction to a primitive on the full cut complement. The endpoint
estimates give full relative limits at both ends of every open real gap.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAbelian_discComplement_subset_rootDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 φ n) :
    ball c R \ sourcePeriodicSegment hp hp1 φ n ⊆ sourceCanonicalRootDomain hp hp1 φ := by
  intro z hz k
  by_cases hkn : k = n
  · subst k; exact hz.2
  · exact (hother (ball_subset_closedBall hz.1)) k hkn

/-- The actual quotient has a primitive on an isolating cut disc, with
no assumption that the selected real gap is open. -/
theorem exists_sourceAbelian_discComplement_primitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    ∃ c : ℂ, ∃ R : ℝ,
      sourcePeriodicSegment hp hp1 φ n ⊆ ball c R ∧
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 φ n ∧
      ∃ F : ℂ → ℂ, ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 φ n,
        HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z /
          sourceCanonicalRoot hp hp1 φ z) z := by
  obtain ⟨V,_,hφV,c,T,hT,hgeom,hperiod⟩ :=
    exists_local_sourceCriticalRootRatio_circleIntegral_zero_allGaps hp hp1 φ hφ n
  obtain ⟨hseg,hother⟩ := hgeom φ hφV
  obtain ⟨r,R,hr,hrR,hRT,hsegr⟩ := exists_nested_radii_of_segment_subset_ball _ _ c T hseg
  have hotherR := (closedBall_subset_closedBall hRT.le).trans hother
  have hzero : (∮ z in C(c,r), deriv (canonicalDiscriminant hp (periodOnePotential φ)) z /
      sourceCanonicalRoot hp hp1 φ z) = 0 := by
    rw [circleIntegral_sourceCriticalRootRatio_eq_of_nested_enclosingCircles
      hp hp1 φ n c c r T hr hT hsegr hseg
      (closedBall_subset_closedBall (hrR.trans hRT).le) hother]
    exact hperiod φ hφV
  have hclosed : IsClosed (sourcePeriodicSegment hp hp1 φ n) := by
    apply IsCompact.isClosed
    change IsCompact (segment ℝ _ _)
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hconv : Convex ℝ (sourcePeriodicSegment hp hp1 φ n) := convex_segment _ _
  have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 φ n
  have hana : AnalyticOnNhd ℂ (fun z =>
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z)
      (closedBall c R \ sourcePeriodicSegment hp hp1 φ n) := by
    apply (sourceCriticalRootRatio_analyticOnNhd hp hp1 φ).mono
    intro z hz k
    by_cases hkn : k = n
    · subst k; exact hz.2
    · exact (hotherR hz.1) k hkn
  obtain ⟨F,hF⟩ := exists_primitive_on_disc_complement_of_zero_period _ c
    (sourceStandardRootMidpoint hp hp1 φ n) r R hr hrR
    (sourcePeriodicSegment hp hp1 φ n) hclosed hmid (hconv.starConvex hmid) hsegr hana hzero
  exact ⟨c,R,hsegr.trans (ball_subset_ball hrR.le),hotherR,F,hF⟩

/-- Both endpoint limits hold along every approach in the cut disc,
not just along one half-plane or a selected connector. -/
theorem exists_sourceAbelian_discPrimitive_endpoint_limits
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 φ n ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 φ n)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re)
    (F : ℂ → ℂ) (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 φ n,
      HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z /
        sourceCanonicalRoot hp hp1 φ z) z) :
    ∃ A B : ℂ,
      Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 φ n]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 A) ∧
      Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 φ n]
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 B) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  let f : ℂ → ℂ := fun z => deriv (canonicalDiscriminant hp (periodOnePotential φ)) z /
    sourceCanonicalRoot hp hp1 φ z
  let D := ball c R \ sourcePeriodicSegment hp hp1 φ n
  have hD := sourceAbelian_discComplement_subset_rootDomain hp hp1 φ n c R hother
  obtain ⟨ε,M,hε,hM,hweighted⟩ :=
    exists_sourceCriticalRootRatio_endpointPunctured_weighted_bound hp hp1 φ hφ n hopen
  have hlr : l ≠ r := fun he => (ne_of_lt hopen) (congrArg Complex.re he)
  have hb (a : ℂ) (ha : a ∈ ({l,r} : Set ℂ)) (z : ℂ) (hz : z ∈ D)
      (hnear : ‖z-a‖ ≤ ε) : ‖f z * (Real.sqrt (((r.re-l.re)/2)*‖z-a‖) : ℂ)‖ ≤ M := by
    have haz : a ≠ z := by
      intro he
      have haK : a ∈ sourcePeriodicSegment hp hp1 φ n := by
        rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha : a = l ∨ a = r) with h | h
        · exact h ▸ left_mem_segment ℝ l r
        · exact h ▸ right_mem_segment ℝ l r
      exact hz.2 (he ▸ haK)
    have h := hweighted a ha z (hD hz) (norm_pos_iff.mpr (sub_ne_zero.mpr haz))
      (by rwa [norm_sub_rev])
    simpa only [f,norm_sub_rev] using h
  have hf : ContinuousOn f D := ((sourceCriticalRootRatio_analyticOnNhd hp hp1 φ).mono hD).continuousOn
  have hδ : 0 < (r.re-l.re)/2 := div_pos (sub_pos.mpr hopen) (by norm_num)
  obtain ⟨A,hA⟩ := exists_primitive_segment_left_boundary_limit f F (ball c R) l r _ M ε
    isOpen_ball (hseg (left_mem_segment ℝ _ _)) hlr hδ hM.le hε hf hF (hb l (by simp))
  obtain ⟨B,hB⟩ := exists_primitive_segment_right_boundary_limit f F (ball c R) l r _ M ε
    isOpen_ball (hseg (right_mem_segment ℝ _ _)) hlr hδ hM.le hε hf hF (hb r (by simp))
  exact ⟨A,B,hA,hB⟩

end NLS.ZakharovShabat
