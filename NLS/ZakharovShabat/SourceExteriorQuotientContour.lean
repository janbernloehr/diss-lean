import NLS.ZakharovShabat.SourceWeightedPrimitiveBoundary
import NLS.ZakharovShabat.SourceFilledGapQuotient

/-! # Actual exterior quotient contours as arcosh integrals

The weight is analytic on every exterior isolating disc and the original
primitive index offsets contribute zero.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- An exterior Cauchy contour equals its actual weighted arcosh-profile integral. -/
theorem filledGapQuotient_exterior_circle_eq_profile (n m : ℤ) (hmn : m ≠ n)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0)
    (x : ℂ) (hx : x ∈ ball (C.discs.center n) (C.discs.outer n))
    (R : ℝ) (hinner : C.discs.inner m ≤ R) (houter : R < C.discs.outer m) :
    (∮ z in C(C.discs.center m,R), C.filledGapQuotient n φ.val z/(z-x)) =
      2*I * ∫ θ in (0:ℝ)..Real.pi,
        (sourceStandardRootHalfGap hp hp1 φ.val m*(Real.sin θ:ℂ)) *
          (sourceRealGapCosineProfile hp hp1 φ.val m θ:ℂ) /
          (sourceStandardRoot hp hp1 φ.val n (sourceCanonicalRootGapPoint hp hp1 φ.val m (Real.cos θ)) *
            (sourceCanonicalRootGapPoint hp hp1 φ.val m (Real.cos θ)-x)) := by
  have hR : 0 < R := (C.discs.inner_pos m).trans_le hinner
  have hseg (z : ℂ) (hz : z ∈ closedBall (C.discs.center m) R) :
      z ∉ sourcePeriodicSegment hp hp1 φ.val n :=
    C.discs.avoids_other φ.val hφ m ((closedBall_subset_closedBall houter.le) hz) n hmn.symm
  have hzx (z : ℂ) (hz : z ∈ closedBall (C.discs.center m) R) : z-x ≠ 0 := by
    intro he
    have hzm := closedBall_subset_ball houter hz
    rw [sub_eq_zero.mp he] at hzm
    exact Set.disjoint_left.mp (C.discs.disjoint n m hmn.symm) hx hzm
  let w : ℂ → ℂ := fun z => -I/(sourceStandardRoot hp hp1 φ.val n z*(z-x))
  have hw : AnalyticOnNhd ℂ w (closedBall (C.discs.center m) R) := by
    intro z hz
    exact analyticAt_const.div
      ((sourceStandardRoot_analyticAt hp hp1 φ.val n z (hseg z hz)).mul
        (analyticAt_id.sub analyticAt_const))
      (mul_ne_zero (sourceStandardRoot_ne_zero_off_segment hp hp1 φ.val n z (hseg z hz)) (hzx z hz))
  have he := C.weighted_primitive_circle_eq_real_profile_index m n φ hφ hgap R hinner houter w hw
  calc
    _ = ∮ z in C(C.discs.center m,R), w z*sourceFullAbelianPrimitive hp hp1 W n (z,φ.val) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      dsimp only
      rw [C.filledGapQuotient_eq_div n φ.val hφ z (hseg z (sphere_subset_closedBall hz))]
      dsimp [w]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by
      rw [he]
      simp only [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp [w]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
