import NLS.ComplexAnalysis.LatticeDiscInverseBound
import NLS.ZakharovShabat.SourceDiagonalLaurentCosine

/-! # Uniform inverse-frequency bounds around the real diagonal

One common isolating family controls reciprocal cosine points on all
noncentral complex gaps. The bound is of order 1/(1+|n|), including
collapsed gaps, and needs no division by a spectral action.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem exists_diagonal_gapPoint_inverse_bound
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realDiagonalSourceLocus p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius) :
    ∃ D : ℝ, 0 < D ∧ ∀ ψ ∈ ball C.discs.source.val C.discs.sourceRadius,
      ∀ n : ℤ, n ≠ 0 → ∀ θ : ℝ,
        ‖(sourceStandardRootMidpoint hp hp1 ψ n+
          sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ : ℂ))⁻¹‖ ≤ D/(1+|(n : ℝ)|) := by
  obtain ⟨B,hB⟩ := C.discs.outer_bounded
  let M := ‖sourcePeriodicMidpointDisplacement hp hp1 φ.val‖
  have hc (n : ℤ) : ‖C.discs.center n-(Real.pi : ℂ)*n‖ ≤ B+M := by
    have hmid : sourceStandardRootMidpoint hp hp1 φ.val n ∈ sourcePeriodicSegment hp hp1 φ.val n :=
      sourcePeriodicMidpoint_mem_segment hp hp1 φ.val n
    have hnear := (mem_ball.mp (C.discs.segment_subset φ.val hφ n hmid)).le
    rw [dist_eq_norm,norm_sub_rev] at hnear
    have hdis : ‖sourceStandardRootMidpoint hp hp1 φ.val n-(Real.pi : ℂ)*n‖ ≤ M := by
      have he : sourceStandardRootMidpoint hp hp1 φ.val n-(Real.pi : ℂ)*n =
          sourcePeriodicMidpointDisplacement hp hp1 φ.val n := by
        rw [sourcePeriodicMidpointDisplacement_apply]
      rw [he]
      exact lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' _ n
    have he : C.discs.center n-(Real.pi : ℂ)*n =
        (C.discs.center n-sourceStandardRootMidpoint hp hp1 φ.val n)+
          (sourceStandardRootMidpoint hp hp1 φ.val n-(Real.pi : ℂ)*n) := by ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add
      (hnear.trans ((C.discs.inner_lt n).le.trans (hB n))) hdis)
  obtain ⟨D,hD,hbound⟩ := exists_latticeDisc_inverse_bound C.discs.center C.discs.outer (B+M) B hc hB
    (fun n hn => C.zero_not_mem_noncentral_disc_of_diagonal_point ⟨φ.val,φ.property.1⟩ hφ φ.property.2 n hn)
  refine ⟨D,hD,?_⟩
  intro ψ hψ n hn θ
  apply hbound n hn
  apply ball_subset_closedBall
  apply C.segment_subset_outer n ψ hψ
  exact sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n (Real.cos θ)
    (Real.neg_one_le_cos θ) (Real.cos_le_one θ)

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
