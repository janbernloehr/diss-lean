import NLS.ZakharovShabat.SourcePrimitivePowerRealIntegral
import NLS.ZakharovShabat.SourceFullAbelianUniformNormalization

/-! # Analytic weights in actual primitive contour integrals

The exact factor -2 and cancellation of primitive index offsets are proved
with the original standard-root orientation.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- An analytic weight may be retained when shrinking an odd primitive contour to its gap. -/
theorem weighted_primitive_odd_circle_eq_boundary (n : ℤ) (m : ℕ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n)
    (w : ℂ → ℂ) (hw : AnalyticOnNhd ℂ w (closedBall (C.discs.center n) R)) :
    (∮ z in C(C.discs.center n,R), w z*(sourceFullAbelianPrimitive hp hp1 W n (z,φ.val))^(2*m+1)) =
      -2 * ∫ θ in (0:ℝ)..Real.pi,
        w (sourceCanonicalRootGapPoint hp hp1 φ.val n (Real.cos θ)) *
          (sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ:ℂ)) *
          (C.gapBoundary n φ.val θ true)^(2*m+1) := by
  have hR : 0 < R := (C.discs.inner_pos n).trans_le hinner
  have hc : ((C.discs.center n).re:ℂ) = C.discs.center n :=
    Complex.ext rfl (by simpa only [ofReal_im] using (C.discs.center_real n).symm)
  have hg : AnalyticOnNhd ℂ (fun z => w z*C.powerNumerator n m φ.val z)
      (closedBall (C.discs.center n) R) :=
    fun z hz => (hw z hz).mul (C.powerNumerator_analytic n m φ.val hφ z (closedBall_subset_ball houter hz))
  have hseg := (C.discs.segment_subset φ.val hφ n).trans (ball_subset_ball hinner)
  have hopen := source_openRealGap_of_realType_gap_ne_zero hp hp1 n φ.val φ.property
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  have he := weighted_sourceStandardRoot_realCenteredCircle_eq_boundary hp hp1 φ.val φ.property n hopen
    (fun z => w z*C.powerNumerator n m φ.val z) (C.discs.center n).re R hR
    (by simpa only [hc] using hseg) (by simpa only [hc] using hg)
  rw [hc,gapSideBoundaryIntegral_eq_primitive _ _ _ _ (div_ne_zero hgap (by norm_num)) true] at he
  simp only [gapSidePrimitive,ite_true,Real.arccos_one] at he
  calc
    _ = ∮ z in C(C.discs.center n,R),
        (w z*C.powerNumerator n m φ.val z)/sourceStandardRoot hp hp1 φ.val n z := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      dsimp only
      rw [C.primitive_odd_eq_weighted n m φ.val hφ z
        ⟨closedBall_subset_ball houter (sphere_subset_closedBall hz),
          C.intermediate_circle_root n φ.val hφ R hinner houter z hz n⟩]
      ring
    _ = _ := by
      rw [he]
      simp only [C.powerNumerator_cosine]
      simp only [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only [sourceCanonicalRootGapPoint]
      ring_nf
      simp only [I_sq]
      ring

/-- The weighted contour of the selected primitive is an integral of the actual arcosh profile. -/
theorem weighted_primitive_circle_eq_real_profile (n : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n)
    (w : ℂ → ℂ) (hw : AnalyticOnNhd ℂ w (closedBall (C.discs.center n) R)) :
    (∮ z in C(C.discs.center n,R), w z*sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)) =
      -2 * ∫ θ in (0:ℝ)..Real.pi,
        w (sourceCanonicalRootGapPoint hp hp1 φ.val n (Real.cos θ)) *
          (sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ:ℂ)) *
          (sourceRealGapCosineProfile hp hp1 φ.val n θ:ℂ) := by
  have he := C.weighted_primitive_odd_circle_eq_boundary n 0 φ hφ hgap R hinner houter w hw
  simp only [mul_zero,zero_add,pow_one] at he
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [uIcc_of_le Real.pi_pos.le] at hθ
  dsimp only
  rw [C.gapBoundary_eq_realCosineProfile n φ hφ hgap θ hθ]


/-- The index normalization contributes no weighted contour when the weight is analytic. -/
theorem weighted_primitive_circle_index_independent (m n : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (R : ℝ) (hinner : C.discs.inner m ≤ R) (houter : R < C.discs.outer m)
    (w : ℂ → ℂ) (hw : AnalyticOnNhd ℂ w (closedBall (C.discs.center m) R)) :
    (∮ z in C(C.discs.center m,R), w z*sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)) =
      ∮ z in C(C.discs.center m,R), w z*sourceFullAbelianPrimitive hp hp1 W m (z,φ.val) := by
  have hR : 0 < R := (C.discs.inner_pos m).trans_le hinner
  obtain ⟨E⟩ := C.charts φ.val hφ
  have hc : CircleIntegrable (fun z => w z*sourceFullAbelianPrimitive hp hp1 W m (z,φ.val))
      (C.discs.center m) R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact ((hw z (sphere_subset_closedBall hz)).continuousAt.mul
      (sourceFullAbelianPrimitive_hasDerivAt E m z
        (C.intermediate_circle_root m φ.val hφ R hinner houter z hz)).continuousAt).continuousWithinAt
  have hd : DifferentiableOn ℂ (fun z => w z*(I*(Real.pi:ℂ)*(n-m)))
      (closedBall (C.discs.center m) R) :=
    fun z hz => ((hw z hz).mul analyticAt_const).differentiableAt.differentiableWithinAt
  have hz := (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn).circleIntegral_eq_zero hR.le
  calc
    _ = ∮ z in C(C.discs.center m,R),
        w z*sourceFullAbelianPrimitive hp hp1 W m (z,φ.val)+w z*(I*(Real.pi:ℂ)*(n-m)) := by
      apply circleIntegral.integral_congr hR.le
      intro z hzs
      dsimp only
      have hzm : z ∈ ball (C.discs.center m) (C.discs.outer m) \ sourcePeriodicSegment hp hp1 φ.val m :=
        ⟨closedBall_subset_ball houter (sphere_subset_closedBall hzs),
          C.intermediate_circle_root m φ.val hφ R hinner houter z hzs m⟩
      rw [C.fullPrimitive_eq_cauchy m n φ.val hφ z hzm,C.fullPrimitive_eq_cauchy m m φ.val hφ z hzm]
      ring
    _ = _ := by
      rw [circleIntegral.integral_add hc (hd.continuousOn.mono sphere_subset_closedBall |>.circleIntegrable hR.le),hz,add_zero]

/-- Any indexed primitive has the same weighted arcosh integral on the chosen gap. -/
theorem weighted_primitive_circle_eq_real_profile_index (m n : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0)
    (R : ℝ) (hinner : C.discs.inner m ≤ R) (houter : R < C.discs.outer m)
    (w : ℂ → ℂ) (hw : AnalyticOnNhd ℂ w (closedBall (C.discs.center m) R)) :
    (∮ z in C(C.discs.center m,R), w z*sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)) =
      -2 * ∫ θ in (0:ℝ)..Real.pi,
        w (sourceCanonicalRootGapPoint hp hp1 φ.val m (Real.cos θ)) *
          (sourceStandardRootHalfGap hp hp1 φ.val m*(Real.sin θ:ℂ)) *
          (sourceRealGapCosineProfile hp hp1 φ.val m θ:ℂ) := by
  rw [C.weighted_primitive_circle_index_independent m n φ hφ R hinner houter w hw]
  exact C.weighted_primitive_circle_eq_real_profile m φ hφ hgap R hinner houter w hw

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
