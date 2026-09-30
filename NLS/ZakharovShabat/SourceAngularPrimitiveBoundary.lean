import NLS.ComplexAnalysis.SegmentPrimitiveBoundary
import NLS.ZakharovShabat.SourceAngularDiscComplementPrimitive
import NLS.ZakharovShabat.SourceAngularEndpointCommonDomain

/-!
# Common limits of actual angular primitives at complex endpoints

The actual endpoint estimate and the full disc-complement primitives
give a single finite limit at each endpoint of a noncollapsed gap.
The limits hold for every approach inside the cut complement, with
no restriction to a half-plane, ray, or prescribed connector.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both endpoint limits of any actual canonical-sheet angular
primitive follow from the spectral data and the proved weighted bound. -/
theorem exists_sourceAngular_primitive_endpoint_limits
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (F : ℂ → ℂ)
    (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m,
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z) :
    ∃ A B : ℂ,
      Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ m]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A) ∧
      Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ m]
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 B) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let f : ℂ → ℂ := fun z => sourceAngularIntegrand n s
    (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)
  let D := ball c R \ sourcePeriodicSegment hp hp1 ψ m
  have hD (z : ℂ) (hz : z ∈ D) : z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
    intro k
    by_cases hkm : k = m
    · subst k
      exact hz.2
    · exact (hother (ball_subset_closedBall hz.1)) k hkm
  obtain ⟨ε,M,hε,hM,hweighted⟩ := exists_sourceAngular_endpoint_weighted_bound
    hp hp1 n m s ψ hdata.isOpen_omitted hdata.gap_avoids_other_gaps hdata.analytic_omitted hgap
  let δ := ‖r-l‖/2
  have hδ : 0 < δ := div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hgap.symm)) (by norm_num)
  have hb (a : ℂ) (ha : a ∈ ({l,r} : Set ℂ)) (z : ℂ) (hz : z ∈ D)
      (hnear : ‖z-a‖ ≤ ε) : ‖f z * (Real.sqrt (δ*‖z-a‖) : ℂ)‖ ≤ M := by
    have h := hweighted a ha z (hD z hz) (by rwa [norm_sub_rev])
      (sourceCanonicalRoot hp hp1 ψ z)
      (sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 ψ z (hD z hz))
    simpa only [f,sourceAngularIntegrand,δ,l,r,norm_sub_rev] using h
  have hf : ContinuousOn f D :=
    (sourceAngular_discComplement_analyticOnNhd hp hp1 n m s ψ c R hother).continuousOn
  have hl : l ∈ ball c R := hseg (left_mem_segment ℝ _ _)
  have hr : r ∈ ball c R := hseg (right_mem_segment ℝ _ _)
  obtain ⟨A,hA⟩ := exists_primitive_segment_left_boundary_limit f F (ball c R) l r δ M ε
    isOpen_ball hl hgap hδ hM.le hε hf hF (hb l (by simp))
  obtain ⟨B,hB⟩ := exists_primitive_segment_right_boundary_limit f F (ball c R) l r δ M ε
    isOpen_ball hr hgap hδ hM.le hε hf hF (hb r (by simp))
  exact ⟨A,B,hA,hB⟩

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The normalized psi family supplies full-domain off-diagonal
primitives and both common endpoint limits, on one all-gap family of
isolating discs. The endpoint data are available on the common open
source neighborhood from `exists_sourceAngularEndpoint_common_domain`. -/
theorem exists_angular_endpoint_primitives
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hdata : ∀ m, SourceAngularEndpointSpectralData hp hp1 ψ m) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ m, 0 < r m ∧ r m < R m ∧
        sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (r m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m) ∧
      ∀ n m, m ≠ n →
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
        ∃ F : ℂ → ℂ, ∃ A B : ℂ,
          (∀ z ∈ ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m,
            HasDerivAt F (sourceAngularIntegrand n s
              (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z) ∧
          Tendsto F (𝓝[ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m]
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A) ∧
          Tendsto F (𝓝[ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m]
            (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 B) := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_angular_discComplement_primitives ψ hψ
  refine ⟨c,r,R,hgeom,?_⟩
  intro n m hmn hgap
  obtain ⟨F,hF⟩ := hprim n m hmn
  obtain ⟨A,B,hA,hB⟩ := exists_sourceAngular_primitive_endpoint_limits hp hp1 n m s ψ (c m) (R m)
    ((hgeom m).2.2.1.trans (ball_subset_ball (hgeom m).2.1.le)) (hgeom m).2.2.2 (hdata m) hgap F hF
  exact ⟨F,A,B,hF,hA,hB⟩

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
