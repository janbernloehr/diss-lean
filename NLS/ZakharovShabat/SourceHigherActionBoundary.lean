import NLS.ZakharovShabat.SourceHigherActionCircle
import NLS.ZakharovShabat.SourceRealHigherAction

/-! # The higher-action contour equals its real gap representation -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- Collapse the spectrally weighted primitive contour onto its actual upper gap boundary. -/
theorem higherActionCircle_eq_boundaryIntegral
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) (k : ℕ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n) :
    sourceHigherActionCircle hp hp1 φ.val (C.discs.center n) R k =
      (2/Real.pi : ℂ) * ∫ θ in (0 : ℝ)..Real.pi,
        (sourceStandardRootMidpoint hp hp1 φ.val n+sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ))^k *
        ((sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ:ℂ))*C.gapBoundary n φ.val θ true) := by
  have hR : 0 < R := (C.discs.inner_pos n).trans_le hinner
  have hc : ((C.discs.center n).re : ℂ) = C.discs.center n :=
    Complex.ext rfl (by simpa only [ofReal_im] using (C.discs.center_real n).symm)
  let g : ℂ → ℂ := fun z => z^k * C.powerNumerator n 0 φ.val z
  have hg : AnalyticOnNhd ℂ g (closedBall (C.discs.center n) R) :=
    fun z hz => (analyticAt_id.pow k).mul
      (C.powerNumerator_analytic n 0 φ.val hφ z (closedBall_subset_ball houter hz))
  have hseg := (C.discs.segment_subset φ.val hφ n).trans (ball_subset_ball hinner)
  have hopen := source_openRealGap_of_realType_gap_ne_zero hp hp1 n φ.val φ.property
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  have he := weighted_sourceStandardRoot_realCenteredCircle_eq_boundary hp hp1 φ.val φ.property n hopen
    g (C.discs.center n).re R hR (by simpa only [hc] using hseg) (by simpa only [hc] using hg)
  rw [hc,gapSideBoundaryIntegral_eq_primitive _ _ _ _ (div_ne_zero hgap (by norm_num)) true] at he
  simp only [gapSidePrimitive,ite_true,Real.arccos_one] at he
  obtain ⟨E⟩ := C.charts φ.val hφ
  rw [sourceHigherActionCircle_eq_primitive hp hp1 W n φ.val E _ _ hR.le
    (C.intermediate_circle_root n φ.val hφ R hinner houter)]
  have hw : (∮ z in C(C.discs.center n,R), z^k*sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)) =
      ∮ z in C(C.discs.center n,R), g z / sourceStandardRoot hp hp1 φ.val n z := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hz' := C.primitive_odd_eq_weighted n 0 φ.val hφ z
      ⟨closedBall_subset_ball houter (sphere_subset_closedBall hz),
        C.intermediate_circle_root n φ.val hφ R hinner houter z hz n⟩
    simp only [Nat.mul_zero,zero_add,pow_one] at hz'
    dsimp only
    rw [hz']
    exact (mul_div_assoc _ _ _).symm
  rw [hw,he]
  have hpoint (θ : ℝ) : g (sourceStandardRootMidpoint hp hp1 φ.val n+
      sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ)) =
      -I * ((sourceStandardRootMidpoint hp hp1 φ.val n+
        sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ))^k *
        ((sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ:ℂ))*C.gapBoundary n φ.val θ true)) := by
    dsimp only [g]
    rw [C.powerNumerator_cosine]
    simp only [Nat.mul_zero,zero_add,pow_one]
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  simp only [I_sq]
  ring

/-- The actual contour computes the higher real action at every open gap. -/
theorem higherActionCircle_eq_real_of_open
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) (k : ℕ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n) :
    sourceHigherActionCircle hp hp1 φ.val (C.discs.center n) R k =
      (sourceRealHigherAction hp hp1 φ n k : ℂ) := by
  rw [C.higherActionCircle_eq_boundaryIntegral n k φ hφ hgap R hinner houter]
  have he : (∫ θ in (0 : ℝ)..Real.pi,
      (sourceStandardRootMidpoint hp hp1 φ.val n+sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ))^k *
      ((sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ:ℂ))*C.gapBoundary n φ.val θ true)) =
      sourceStandardRootHalfGap hp hp1 φ.val n *
        ∫ θ in (0 : ℝ)..Real.pi, (((realGapAffinePoint hp hp1 φ.val n (Real.cos θ))^k *
          (Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le Real.pi_pos.le] at hθ
    dsimp only
    rw [C.gapBoundary_eq_realCosineProfile n φ hφ hgap θ hθ]
    have hx := sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint hp hp1 φ.val φ.property n (Real.cos θ)
    change sourceStandardRootMidpoint hp hp1 φ.val n+sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ) = _ at hx
    rw [hx]
    simp only [ofReal_mul,ofReal_pow]
    ring
  rw [he,intervalIntegral.integral_ofReal,sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 φ.val φ.property n]
  simp only [sourceRealHigherAction,ofReal_mul,ofReal_div,ofReal_sub,ofReal_ofNat,canonicalPeriodicGap,sub_re]
  ring

/-- Every polynomially weighted action contour vanishes at a collapsed gap. -/
theorem higherActionCircle_eq_zero_of_collapsed
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) (k : ℕ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n) :
    sourceHigherActionCircle hp hp1 φ.val (C.discs.center n) R k = 0 := by
  have hR : 0 ≤ R := (C.discs.inner_pos n).le.trans hinner
  obtain ⟨E⟩ := C.charts φ.val hφ
  rw [sourceHigherActionCircle_eq_primitive hp hp1 W n φ.val E _ _ hR
    (C.intermediate_circle_root n φ.val hφ R hinner houter)]
  let Q : ℂ → ℂ := fun z => sourceFullAbelianCauchyQuotient hp hp1 W n
    (C.discs.center n) (C.discs.outer n) (z,φ.val)
  let H : ℂ → ℂ := fun z => z^k * ((sourceStandardRootMidpoint hp hp1 φ.val n-z)*Q z)
  have hH : AnalyticOnNhd ℂ H (ball (C.discs.center n) (C.discs.outer n)) :=
    fun z hz => (analyticAt_id.pow k).mul ((analyticAt_const.sub analyticAt_id).mul
      (C.quotient_slice_analytic n φ.val hφ z hz))
  have hd : DifferentiableOn ℂ H (closedBall (C.discs.center n) R) :=
    fun z hz => (hH z (closedBall_subset_ball houter hz)).differentiableAt.differentiableWithinAt
  have hz := (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn).circleIntegral_eq_zero hR
  have he : (∮ z in C(C.discs.center n,R), z^k*sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)) =
      ∮ z in C(C.discs.center n,R), H z := by
    apply circleIntegral.integral_congr hR
    intro z hzc
    dsimp only
    rw [C.fullPrimitive_eq_cauchy n n φ.val hφ z
      ⟨closedBall_subset_ball houter (sphere_subset_closedBall hzc),
        C.intermediate_circle_root n φ.val hφ R hinner houter z hzc n⟩]
    simp only [sub_self,mul_zero,add_zero,sourceFullAbelianCauchyPrimitive,
      sourceStandardRoot_of_zeroGap hp hp1 φ.val n z hgap,sourceStandardRootMidpoint,H,Q]
  rw [he,hz,mul_zero]

/-- Every admissible real circle computes the same intrinsic higher-level action,
including collapsed gaps and every natural level. -/
theorem higherActionCircle_eq_real
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) (k : ℕ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n) :
    sourceHigherActionCircle hp hp1 φ.val (C.discs.center n) R k =
      (sourceRealHigherAction hp hp1 φ n k : ℂ) := by
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0
  · rw [C.higherActionCircle_eq_zero_of_collapsed n k φ hφ hgap R hinner houter,
      sourceRealHigherAction_of_collapsed hp hp1 φ n hgap k,ofReal_zero]
  · exact C.higherActionCircle_eq_real_of_open n k φ hφ hgap R hinner houter

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real higher actions come from actual defining contours, with one family
of positive-radius circles for all indices and levels. No chart is assumed. -/
theorem exists_sourceHigherAction_contours (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, (∀ n, 0 < R n) ∧
      ∀ n k, sourceHigherActionCircle hp hp1 φ.val (c n) (R n) k =
        (sourceRealHigherAction hp hp1 φ n k : ℂ) := by
  obtain ⟨W,_,_,hC⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hcenter⟩ := hC φ
  have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact mem_ball_self C.discs.sourceRadius_pos
  let R : ℤ → ℝ := fun n => (C.discs.inner n+C.discs.outer n)/2
  have hi (n : ℤ) : C.discs.inner n ≤ R n := by dsimp [R]; linarith [C.discs.inner_lt n]
  have ho (n : ℤ) : R n < C.discs.outer n := by dsimp [R]; linarith [C.discs.inner_lt n]
  exact ⟨C.discs.center,R,fun n => (C.discs.inner_pos n).trans_le (hi n),
    fun n k => C.higherActionCircle_eq_real n k φ hφ (R n) (hi n) (ho n)⟩

end NLS.ZakharovShabat
