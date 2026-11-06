import NLS.ZakharovShabat.SourceHigherActionBoundary

/-! # Holomorphically weighted actual primitive contours

The source's primitive contour may carry any weight analytic on its
closed isolating disc. The real gap formula and collapsed-gap vanishing
therefore apply to Laurent weights whenever the disc excludes zero.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceWeightedPrimitiveCircle (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (w : ℂ → ℂ) : ℂ :=
  -(Real.pi : ℂ)⁻¹ * ∮ z in C(c,R), w z*sourceFullAbelianPrimitive hp hp1 W n (z,ψ)

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem weightedPrimitiveCircle_eq_boundaryIntegral
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n)
    (w : ℂ → ℂ) (hw : AnalyticOnNhd ℂ w (closedBall (C.discs.center n) R)) :
    sourceWeightedPrimitiveCircle hp hp1 W n φ.val (C.discs.center n) R w =
      (2/Real.pi : ℂ) * ∫ θ in (0 : ℝ)..Real.pi,
        w (sourceStandardRootMidpoint hp hp1 φ.val n+sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ)) *
        ((sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ:ℂ))*C.gapBoundary n φ.val θ true) := by
  have hR : 0 < R := (C.discs.inner_pos n).trans_le hinner
  have hc : ((C.discs.center n).re : ℂ) = C.discs.center n :=
    Complex.ext rfl (by simpa only [ofReal_im] using (C.discs.center_real n).symm)
  let g : ℂ → ℂ := fun z => w z*C.powerNumerator n 0 φ.val z
  have hg : AnalyticOnNhd ℂ g (closedBall (C.discs.center n) R) :=
    fun z hz => (hw z hz).mul (C.powerNumerator_analytic n 0 φ.val hφ z (closedBall_subset_ball houter hz))
  have hseg := (C.discs.segment_subset φ.val hφ n).trans (ball_subset_ball hinner)
  have hopen := source_openRealGap_of_realType_gap_ne_zero hp hp1 n φ.val φ.property
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  have he := weighted_sourceStandardRoot_realCenteredCircle_eq_boundary hp hp1 φ.val φ.property n hopen
    g (C.discs.center n).re R hR (by simpa only [hc] using hseg) (by simpa only [hc] using hg)
  rw [hc,gapSideBoundaryIntegral_eq_primitive _ _ _ _ (div_ne_zero hgap (by norm_num)) true] at he
  simp only [gapSidePrimitive,ite_true,Real.arccos_one] at he
  have hi : (∮ z in C(C.discs.center n,R), w z*sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)) =
      ∮ z in C(C.discs.center n,R), g z/sourceStandardRoot hp hp1 φ.val n z := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hz' := C.primitive_odd_eq_weighted n 0 φ.val hφ z
      ⟨closedBall_subset_ball houter (sphere_subset_closedBall hz),
        C.intermediate_circle_root n φ.val hφ R hinner houter z hz n⟩
    simp only [Nat.mul_zero,zero_add,pow_one] at hz'
    dsimp only
    rw [hz']
    exact (mul_div_assoc _ _ _).symm
  rw [sourceWeightedPrimitiveCircle,hi,he]
  have hpoint (θ : ℝ) : g (sourceStandardRootMidpoint hp hp1 φ.val n+
      sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ)) =
      -I*(w (sourceStandardRootMidpoint hp hp1 φ.val n+
        sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ))*
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

theorem weightedPrimitiveCircle_eq_zero_of_collapsed
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n)
    (w : ℂ → ℂ) (hw : AnalyticOnNhd ℂ w (closedBall (C.discs.center n) R)) :
    sourceWeightedPrimitiveCircle hp hp1 W n φ.val (C.discs.center n) R w = 0 := by
  have hR : 0 ≤ R := (C.discs.inner_pos n).le.trans hinner
  let Q : ℂ → ℂ := fun z => sourceFullAbelianCauchyQuotient hp hp1 W n
    (C.discs.center n) (C.discs.outer n) (z,φ.val)
  let H : ℂ → ℂ := fun z => w z*((sourceStandardRootMidpoint hp hp1 φ.val n-z)*Q z)
  have hH : AnalyticOnNhd ℂ H (closedBall (C.discs.center n) R) :=
    fun z hz => (hw z hz).mul ((analyticAt_const.sub analyticAt_id).mul
      (C.quotient_slice_analytic n φ.val hφ z (closedBall_subset_ball houter hz)))
  have hd : DifferentiableOn ℂ H (closedBall (C.discs.center n) R) := hH.differentiableOn
  have hz := (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn).circleIntegral_eq_zero hR
  have he : (∮ z in C(C.discs.center n,R), w z*sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)) =
      ∮ z in C(C.discs.center n,R), H z := by
    apply circleIntegral.integral_congr hR
    intro z hzc
    dsimp only
    rw [C.fullPrimitive_eq_cauchy n n φ.val hφ z
      ⟨closedBall_subset_ball houter (sphere_subset_closedBall hzc),
        C.intermediate_circle_root n φ.val hφ R hinner houter z hzc n⟩]
    simp only [sub_self,mul_zero,add_zero,sourceFullAbelianCauchyPrimitive,
      sourceStandardRoot_of_zeroGap hp hp1 φ.val n z hgap,sourceStandardRootMidpoint,H,Q]
  rw [sourceWeightedPrimitiveCircle,he,hz,mul_zero]

/-- Every analytic weight has the exact real-gap representation,
including collapsed gaps. No division by the gap length occurs. -/
theorem weightedPrimitiveCircle_eq_realIntegral
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n)
    (w : ℂ → ℂ) (hw : AnalyticOnNhd ℂ w (closedBall (C.discs.center n) R)) :
    sourceWeightedPrimitiveCircle hp hp1 W n φ.val (C.discs.center n) R w =
      ((canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re : ℂ) /
        (Real.pi : ℂ) * ∫ θ in (0 : ℝ)..Real.pi,
          w (realGapAffinePoint hp hp1 φ.val n (Real.cos θ)) *
            ((Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ : ℝ) : ℂ) := by
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0
  · rw [C.weightedPrimitiveCircle_eq_zero_of_collapsed n φ hφ hgap R hinner houter w hw,hgap]
    simp only [zero_re,ofReal_zero,zero_div,zero_mul]
  · rw [C.weightedPrimitiveCircle_eq_boundaryIntegral n φ hφ hgap R hinner houter w hw]
    have he : (∫ θ in (0 : ℝ)..Real.pi,
        w (sourceStandardRootMidpoint hp hp1 φ.val n+sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ))*
        ((sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ:ℂ))*C.gapBoundary n φ.val θ true)) =
        sourceStandardRootHalfGap hp hp1 φ.val n * ∫ θ in (0 : ℝ)..Real.pi,
          w (realGapAffinePoint hp hp1 φ.val n (Real.cos θ)) *
            ((Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le Real.pi_pos.le] at hθ
      dsimp only
      rw [C.gapBoundary_eq_realCosineProfile n φ hφ hgap θ hθ]
      have hx := sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint hp hp1 φ.val φ.property n (Real.cos θ)
      change sourceStandardRootMidpoint hp hp1 φ.val n+
        sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ) = _ at hx
      rw [hx]
      simp only [ofReal_mul]
      ring
    rw [he,sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 φ.val φ.property n]
    simp only [ofReal_div,ofReal_sub,ofReal_ofNat,canonicalPeriodicGap,sub_re]
    ring

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
