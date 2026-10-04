import NLS.ZakharovShabat.SourceAbelianComplexDiscContinuation
import NLS.ZakharovShabat.SourceStandardRootComplexEndpointBound
import NLS.ZakharovShabat.SourceCriticalRootGapNeighborhood

/-! # Full endpoint limits of complex-source abelian disc primitives

The regular numerator is bounded on a closed isolating disc. The modulus
of the standard root then gives inverse-square-root growth near either
endpoint of a nondegenerate complex gap, with no reality or ordering
assumption. Every primitive has a finite limit along the full cut disc.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One weighted bound applies at both complex endpoints. The gap
 length is its complex norm, so vertical gaps are included. -/
theorem exists_sourceCriticalRootRatio_complexEndpoint_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (j : ℤ) (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ j)
    (hE : AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 j ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ j)) :
    ∃ M : ℝ, 0 < M ∧ ∀ a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j} : Set ℂ),
      ∀ z ∈ closedBall c R, z ∈ sourceCanonicalRootDomain hp hp1 ψ →
        ‖z-a‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖/2 →
        ‖(deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) *
          (Real.sqrt ((‖sourcePeriodicGapDisplacement hp hp1 ψ j‖/2)*‖z-a‖) : ℂ)‖ ≤ M := by
  have hnum : ContinuousOn (sourceCriticalRootGapNumerator hp hp1 ψ j) (closedBall c R) := by
    intro z hz
    exact ((continuousAt_const.sub continuousAt_id).mul (hE z (hother hz)).continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hnum
  let M := max C 0+1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M,hM,?_⟩
  intro a ha z hz hroot hnear
  have hn : ‖sourceCriticalRootGapNumerator hp hp1 ψ j z‖ ≤ M :=
    (hC z hz).trans (by dsimp [M]; linarith [le_max_left C 0])
  have hs := sourceStandardRoot_complexEndpoint_norm_lower_bound hp hp1 ψ j a z ha (hroot j)
    (by simpa only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,norm_sub_rev] using hnear)
  have heq : deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z =
      sourceCriticalRootGapNumerator hp hp1 ψ j z / sourceStandardRoot hp hp1 ψ j z := by
    rw [sourceCriticalRootRatio_eq_selectedFactor_mul_extension hp hp1 ψ j z hroot]
    unfold sourceCriticalRootGapNumerator
    simp only [div_eq_mul_inv]
    ring
  rw [heq]
  apply norm_div_mul_real_le_of_weight_le_norm _ _ _ M (Real.sqrt_nonneg _) hM.le hn
    _ (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ j z (hroot j))
  simpa only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,norm_sub_rev] using hs

/-- Every primitive on a complex cut disc has a full relative limit at
 both distinct endpoints, rather than only along a selected approach. -/
theorem exists_sourceAbelian_complexDisc_endpoint_limits
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (j : ℤ) (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ j ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ j)
    (hE : AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 j ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ j))
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ j ≠ 0)
    (F : ℂ → ℂ) (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ j,
      HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z) :
    ∃ A B : ℂ,
      Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ j]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)) (𝓝 A) ∧
      Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ j]
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)) (𝓝 B) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j
  let δ := ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖/2
  have hδ : 0 < δ := div_pos (norm_pos_iff.mpr hgap) (by norm_num)
  have hlr : l ≠ r := by
    intro he
    apply hgap
    rw [sourcePeriodicGapDisplacement_apply]
    exact sub_eq_zero.mpr he.symm
  have hroot := sourceAbelian_discComplement_subset_rootDomain hp hp1 ψ j c R hother
  have hf := ((sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ).mono hroot).continuousOn
  obtain ⟨M,hM,hbound⟩ := exists_sourceCriticalRootRatio_complexEndpoint_bound hp hp1 ψ j c R hother hE
  obtain ⟨A,hA⟩ := exists_primitive_segment_left_boundary_limit _ F (ball c R) l r δ M δ
    isOpen_ball (hseg (left_mem_segment ℝ _ _)) hlr hδ hM.le hδ hf hF
    (fun z hz hnear => hbound l (by simp [l]) z (ball_subset_closedBall hz.1) (hroot hz) hnear)
  obtain ⟨B,hB⟩ := exists_primitive_segment_right_boundary_limit _ F (ball c R) l r δ M δ
    isOpen_ball (hseg (right_mem_segment ℝ _ _)) hlr hδ hM.le hδ hf hF
    (fun z hz hnear => hbound r (by simp [r]) z (ball_subset_closedBall hz.1) (hroot hz) hnear)
  exact ⟨A,B,hA,hB⟩

end NLS.ZakharovShabat
