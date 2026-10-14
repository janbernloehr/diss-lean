import NLS.ZakharovShabat.SourceCriticalRootOriginalDiscPrimitive
import NLS.ZakharovShabat.SourceAbelianComplexCollapsedExtension
import NLS.ComplexAnalysis.CosinePrimitiveEndpointAgreement

/-!
# Equal endpoint limits on the original complex cut disks

Every primitive of the actual critical-root quotient has a common finite
limit at the two periodic endpoints. The noncollapsed case uses full
relative endpoint estimates and the opposite cosine sheet coefficients.
A collapsed cut is filled analytically, without changing the primitive
on its original domain. All conclusions retain the existing source W.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any primitive on the original cut disk has equal endpoint values,
including collapsed and non-real gaps. -/
theorem SourceLemma10_11CircleData.cutDisc_common_endpoint_limit
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (D : SourceCriticalRootPeriodCircle hp hp1 ψ n)
    (F : ℂ → ℂ) (hF : ∀ z ∈ ball (D.center : ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt F (sourceCriticalRootRatioJoint hp hp1 (z,ψ)) z) :
    ∃ A : ℂ,
      Tendsto F (𝓝[ball (D.center : ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ n]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 A) ∧
      Tendsto F (𝓝[ball (D.center : ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ n]
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 A) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let hEq := h.previous.previous
  have hE := hEq.previous.previous.previous.previous.criticalRatioExtension ψ hψ n
  have hother := D.closedBall_subset_omittedDomain
  have hroot := sourceAbelian_discComplement_subset_rootDomain hp hp1 ψ n _ _ hother
  by_cases hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
  · have hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 := by
      simpa only [sourcePeriodicGapDisplacement_apply] using hgap
    have he : r = l := sub_eq_zero.mp hg
    have hag : AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 n ψ)
        (ball (D.center : ℂ) D.radius) := hE.mono (ball_subset_closedBall.trans hother)
    have heq : EqOn (sourceCriticalRootRatioExtension hp hp1 n ψ)
        (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z/sourceCanonicalRoot hp hp1 ψ z)
        (ball (D.center : ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ n) := by
      intro z hz
      exact (hEq.continued_eq_extension ψ hψ n hg z (hother (ball_subset_closedBall hz.1))).symm.trans
        (hEq.continued_eq_quotient ψ hψ z (hroot hz))
    obtain ⟨H,_,_,_,hlim⟩ := exists_sourceAbelian_complexDisc_extension_of_derivative_extension
      hp hp1 ψ n _ _ D.gap F (sourceCriticalRootRatioExtension hp hp1 n ψ) hag hF heq
    have hl := hlim l (D.gap (left_mem_segment ℝ _ _))
    refine ⟨H l,hl,?_⟩
    change Tendsto F (𝓝[ball (D.center : ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ n] r) (𝓝 (H l))
    rw [he]
    exact hl
  · have hlr : l ≠ r := by
      intro he
      apply hgap
      rw [sourcePeriodicGapDisplacement_apply]
      exact sub_eq_zero.mpr he.symm
    let τ := (l+r)/2
    let δ := (r-l)/2
    have hl : τ-δ = l := by dsimp [τ,δ]; ring
    have hr : τ+δ = r := by dsimp [τ,δ]; ring
    have hδ : δ ≠ 0 := div_ne_zero (sub_ne_zero.mpr hlr.symm) (by norm_num)
    obtain ⟨A,B,hA,hB⟩ := exists_sourceAbelian_complexDisc_endpoint_limits
      hp hp1 ψ n _ _ D.gap hother hE hgap F hF
    have hab : A = B := by
      apply primitive_cosine_gap_boundary_values_eq
        (sourceCriticalRootGapNumerator hp hp1 ψ n) (sourceStandardRoot hp hp1 ψ n)
        F (ball (D.center : ℂ) D.radius) τ δ A B isOpen_ball hδ
      · rw [hl,hr]; exact D.gap
      · intro z hz
        exact (analyticAt_const.sub analyticAt_id).mul (hE z (hother (ball_subset_closedBall hz)))
      · rw [hl,hr]
        intro z hz
        exact (sourceStandardRoot_analyticAt hp hp1 ψ n z hz.2).continuousAt.continuousWithinAt
      · rw [hl,hr]
        intro z hz
        exact sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ n z hz.2
      · rw [hl,hr]
        intro z hz
        have heq : sourceCriticalRootRatioJoint hp hp1 (z,ψ) =
            sourceCriticalRootGapNumerator hp hp1 ψ n z/sourceStandardRoot hp hp1 ψ n z := by
          rw [sourceCriticalRootRatioJoint,sourceCriticalRootRatio_eq_selectedFactor_mul_extension hp hp1 ψ n z (hroot hz)]
          unfold sourceCriticalRootGapNumerator
          ring
        rw [← heq]
        exact hF z hz
      · rw [hl,hr]; exact hA
      · rw [hl,hr]; exact hB
    exact ⟨A,hA,hab.symm ▸ hB⟩

/-- The actual primitive and its common boundary value exist on the full
original disk, before any admissible path is chosen. -/
theorem SourceLemma10_11CircleData.originalDisk_common_endpoint_primitive
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V) (n : ℤ) :
    ∃ F : ℂ → ℂ, ∃ A : ℂ,
      (∀ z ∈ D n \ sourcePeriodicSegment hp hp1 ψ n,
        HasDerivAt F (sourceCriticalRootRatioJoint hp hp1 (z,ψ)) z) ∧
      Tendsto F (𝓝[D n \ sourcePeriodicSegment hp hp1 ψ n]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 A) ∧
      Tendsto F (𝓝[D n \ sourcePeriodicSegment hp hp1 ψ n]
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 A) := by
  obtain ⟨a,r,hr,he⟩ := hD.discs n
  let C := hD.periodCircle ψ hψV n a r hr he
  obtain ⟨F,hF⟩ := h.exists_cutDisc_primitive ψ hψW n C
  obtain ⟨A,hA,hB⟩ := h.cutDisc_common_endpoint_limit ψ hψW n C F hF
  rw [he]
  exact ⟨F,A,hF,hA,hB⟩

end NLS.ZakharovShabat
