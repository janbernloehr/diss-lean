import NLS.ZakharovShabat.SourceFullAbelianGapComparison
import NLS.ComplexAnalysis.CompactParameterBounds

/-! # Uniform error bounds on a finite collection of central gaps

Joint analyticity bounds the Cauchy quotient on the compact inner discs
after one source-neighborhood restriction. Multiplication by the standard
root restores a factor of the gap length, even as a gap collapses.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- A bounded Cauchy-quotient error gives a bound proportional to the
gap length, uniformly over the whole boundary and its two sides. -/
theorem gapBoundary_sub_root_norm_le_of_quotient
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (ψ : CoeffPair p) (B : ℝ)
    (hb : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ j,
      ‖sourceFullAbelianCauchyQuotient hp hp1 W j (C.discs.center j) (C.discs.outer j) (z,ψ)-I‖ ≤ B)
    (θ : ℝ) (upper : Bool) :
    ‖C.gapBoundary j ψ θ upper-I*sourceStandardRootGapBoundary hp hp1 ψ j θ upper‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖*B := by
  let z := sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j*(Real.cos θ:ℂ)
  let Q := sourceFullAbelianCauchyQuotient hp hp1 W j (C.discs.center j) (C.discs.outer j) (z,ψ)-I
  have hz : z ∈ sourcePeriodicSegment hp hp1 ψ j := by
    rw [sourcePeriodicSegment_eq_midpoint_segment]
    simpa only [z,cosineGapPoint,← Complex.ofReal_cos] using
      cosineGapPoint_real_mem_segment (sourceStandardRootMidpoint hp hp1 ψ j) (sourceStandardRootHalfGap hp hp1 ψ j) θ
  have he : C.gapBoundary j ψ θ upper-I*sourceStandardRootGapBoundary hp hp1 ψ j θ upper =
      (if upper then -I else I)*(sourceStandardRootHalfGap hp hp1 ψ j*(Real.sin θ:ℂ)*Q) := by
    dsimp [gapBoundary,sourceStandardRootGapBoundary,Q,z]
    ring
  have hhalf : ‖sourceStandardRootHalfGap hp hp1 ψ j‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖ := by
    simp only [sourceStandardRootHalfGap,sourcePeriodicGapDisplacement_apply,norm_div,norm_ofNat]
    linarith [norm_nonneg (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)]
  have hs : ‖(Real.sin θ:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one θ
  have h := mul_le_mul (mul_le_mul hhalf hs (norm_nonneg _) (norm_nonneg _))
    (hb z hz) (norm_nonneg _) (by positivity : 0 ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖*1)
  rw [he]
  cases upper <;> simpa only [Bool.false_eq_true,↓reduceIte,norm_mul,norm_neg,norm_I,one_mul,mul_one,Q] using h

/-- A single gap has a uniform linear error bound near any source in
the Cauchy-family ball, including when that gap is collapsed. -/
theorem exists_local_gap_comparison_bound
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : CoeffPair p)
    (hφ : φ ∈ ball C.discs.source.val C.discs.sourceRadius) (j : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ ψ ∈ V ∩ ball C.discs.source.val C.discs.sourceRadius, ∀ θ : ℝ, ∀ upper : Bool,
        ‖C.gapBoundary j ψ θ upper-I*sourceStandardRootGapBoundary hp hp1 ψ j θ upper‖ ≤
          ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖*B := by
  obtain ⟨V,hV,hφV,B,hB,hb⟩ := exists_local_uniform_bound_on_compact_of_continuousOn
    (fun t => sourceFullAbelianCauchyQuotient hp hp1 W j (C.discs.center j) (C.discs.outer j) t-I)
    (ball (C.discs.center j) (C.discs.outer j) ×ˢ ball C.discs.source.val C.discs.sourceRadius)
    (isOpen_ball.prod isOpen_ball)
    ((C.quotient_analytic j).continuousOn.sub continuousOn_const)
    (closedBall (C.discs.center j) (C.discs.inner j)) (isCompact_closedBall _ _) φ
    (fun z hz => ⟨closedBall_subset_ball (C.discs.inner_lt j) hz,hφ⟩)
  refine ⟨V,hV,hφV,B,hB,?_⟩
  intro ψ hψ θ upper
  apply C.gapBoundary_sub_root_norm_le_of_quotient j ψ B _ θ upper
  intro z hz
  exact (hb ψ hψ.1 z (ball_subset_closedBall (C.discs.segment_subset ψ hψ.2 j hz))).2

/-- Every finite set of gaps admits one source neighborhood and one
linear error bound, independent of side and boundary point. -/
theorem exists_local_finite_gap_comparison_bound
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : CoeffPair p)
    (hφ : φ ∈ ball C.discs.source.val C.discs.sourceRadius) (s : Finset ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ ball C.discs.source.val C.discs.sourceRadius ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ ψ ∈ V, ∀ j ∈ s, ∀ θ : ℝ, ∀ upper : Bool,
        ‖C.gapBoundary j ψ θ upper-I*sourceStandardRootGapBoundary hp hp1 ψ j θ upper‖ ≤
          ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖*B := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨_,isOpen_ball,hφ,Subset.rfl,0,le_rfl,by simp⟩
  | @insert j s hj ih =>
    obtain ⟨Vs,hVs,hφs,hsub,Bs,hBs,hbs⟩ := ih
    obtain ⟨Vj,hVj,hφj,Bj,hBj,hbj⟩ := C.exists_local_gap_comparison_bound φ hφ j
    refine ⟨Vs ∩ Vj,hVs.inter hVj,⟨hφs,hφj⟩,inter_subset_left.trans hsub,
      max Bj Bs,hBj.trans (le_max_left _ _),?_⟩
    intro ψ hψ k hk θ upper
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact (hbj ψ ⟨hψ.2,hsub hψ.1⟩ θ upper).trans
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _))
    · exact (hbs ψ hψ.1 k hk θ upper).trans
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _))

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
