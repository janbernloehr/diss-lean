import NLS.ZakharovShabat.SourceFullAbelianGapBoundary
import NLS.ComplexAnalysis.CompactParameterBounds

/-! # Locally uniform bounds for the short endpoint pieces in F.2

Compactness of the fixed inner spectral disc bounds the joint Cauchy
quotient on one source neighborhood. Its literal boundary formula then
bounds both short pieces by one constant times the gap, including at
complex collapsed gaps. No regular-factor bound is assumed.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- One neighborhood and one positive constant control every point and both sides of a fixed gap. -/
theorem appendixF_exists_local_uniform_gapBoundary_bound (φ : CoeffPair p)
    (hφ : φ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      V ⊆ ball C.discs.source.val C.discs.sourceRadius ∧
      ∃ B : ℝ, 0 < B ∧ ∀ ψ ∈ V, ∀ θ : ℝ, ∀ upper : Bool,
        ‖C.gapBoundary n ψ θ upper‖ ≤ B*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
  let Q := sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n)
  let K := closedBall (C.discs.center n) (C.discs.inner n)
  obtain ⟨U,hU,hφU,B,hB,hbound⟩ := exists_local_uniform_bound_on_compact_of_continuousOn
    Q (ball (C.discs.center n) (C.discs.outer n) ×ˢ
      ball C.discs.source.val C.discs.sourceRadius) (isOpen_ball.prod isOpen_ball)
    (C.quotient_analytic n).continuousOn K (isCompact_closedBall _ _) φ
    (fun z hz => ⟨(closedBall_subset_ball (C.discs.inner_lt n)) hz,hφ⟩)
  refine ⟨U ∩ ball C.discs.source.val C.discs.sourceRadius,hU.inter isOpen_ball,
    ⟨hφU,hφ⟩,inter_subset_right,B+1,by positivity,?_⟩
  intro ψ hψ θ upper
  let z := sourceStandardRootMidpoint hp hp1 ψ n+
    sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ)
  have hz : z ∈ sourcePeriodicSegment hp hp1 ψ n := by
    rw [sourcePeriodicSegment_eq_midpoint_segment]
    simpa only [z,cosineGapPoint,← Complex.ofReal_cos] using
      cosineGapPoint_real_mem_segment (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n) θ
  have hQ : ‖Q (z,ψ)‖ ≤ B := (hbound ψ hψ.1 z (ball_subset_closedBall
    (C.discs.segment_subset ψ hψ.2 n hz))).2
  have hs : ‖(Real.sin θ:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact Real.abs_sin_le_one θ
  have hd : ‖sourceStandardRootHalfGap hp hp1 ψ n‖ =
      ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖/2 := by
    simp only [sourceStandardRootHalfGap,norm_div,Complex.norm_ofNat,sourcePeriodicGapDisplacement_apply]
  have hn : ‖C.gapBoundary n ψ θ upper‖ =
      ‖sourceStandardRootHalfGap hp hp1 ψ n‖*‖(Real.sin θ:ℂ)‖*‖Q (z,ψ)‖ := by
    cases upper <;> simp only [gapBoundary,Bool.false_eq_true,↓reduceIte,
      norm_mul,norm_neg,norm_I,one_mul,Q,z]
  rw [hn,hd]
  have hmul := mul_le_mul (mul_le_mul_of_nonneg_left hs
    (div_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2))) hQ
      (norm_nonneg _) (by positivity : 0 ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖/2*1)
  nlinarith [norm_nonneg (sourcePeriodicGapDisplacement hp hp1 ψ n)]

/-- The actual short pieces vanish for arbitrary independently selected angles and sides. -/
theorem appendixF_gapBoundary_tendsto_zero_locally {ι : Type*} {l : Filter ι}
    (φ : CoeffPair p) (hφ : φ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (ψ : ι → CoeffPair p) (hψ : Tendsto ψ l (𝓝 φ)) (n : ℤ)
    (hgap : Tendsto (fun i => ‖sourcePeriodicGapDisplacement hp hp1 (ψ i) n‖) l (𝓝 0))
    (θ : ι → ℝ) (upper : ι → Bool) :
    Tendsto (fun i => C.gapBoundary n (ψ i) (θ i) (upper i)) l (𝓝 0) := by
  obtain ⟨V,hV,hφV,_,B,_,hb⟩ := C.appendixF_exists_local_uniform_gapBoundary_bound φ hφ n
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
    (by simpa only [mul_zero] using hgap.const_mul B)
  filter_upwards [hψ (hV.mem_nhds hφV)] with i hi
  exact hb (ψ i) hi (θ i) (upper i)

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
