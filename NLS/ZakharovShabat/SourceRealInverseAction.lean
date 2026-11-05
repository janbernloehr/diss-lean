import NLS.ZakharovShabat.SourceWeightedPrimitiveBoundaryIntegral
import NLS.ZakharovShabat.SourceFullAbelianInverseGapCircle

/-! The literal inverse-frequency real gap moment. Every selected
nonzero-frequency contour equals this SAME actual cosine gap integral,
including collapsed gaps, with the original -1/pi normalization. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceRealInverseAction (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) : ℝ :=
  (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re/Real.pi *
    ∫ θ in (0:ℝ)..Real.pi, (realGapAffinePoint hp hp1 φ.val n (Real.cos θ))⁻¹ *
      (Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ)

theorem sourceRealInverseAction_of_collapsed (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n=0) :
    sourceRealInverseAction hp hp1 φ n=0 := by
  simp only [sourceRealInverseAction,hg,zero_re,zero_div,zero_mul]

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem inverse_primitive_circle_eq_real_inverseAction
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (R : ℝ) (hi : C.discs.inner n ≤ R) (ho : R < C.discs.outer n)
    (hz : (0:ℂ) ∉ closedBall (C.discs.center n) R) :
    -(Real.pi:ℂ)⁻¹*(∮ z in C(C.discs.center n,R),
      sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)/z)=
        (sourceRealInverseAction hp hp1 φ n:ℂ) := by
  have hR : 0 ≤ R := (C.discs.inner_pos n).le.trans hi
  have hq : AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) (closedBall (C.discs.center n) R) :=
    fun z hzc => analyticAt_id.inv (fun he => hz (he ▸ hzc))
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n=0
  · obtain ⟨D⟩ := C.charts φ.val hφ
    have hF : AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)/z)
        (closedBall (C.discs.center n) R) := by
      intro z hzc
      exact (sourceFullAbelianPrimitive_spectral_analytic D n z
        (C.ball_subset_openGapComplement_of_collapsed n φ.val hφ hgap
          (closedBall_subset_ball ho hzc))).div analyticAt_id (fun he => hz (he ▸ hzc))
    have hzero := (DiffContOnCl.mk_ball (hF.differentiableOn.mono ball_subset_closedBall)
      hF.continuousOn).circleIntegral_eq_zero hR
    rw [hzero,sourceRealInverseAction_of_collapsed hp hp1 φ n hgap]
    simp
  · have hw := C.weighted_primitive_circle_eq_boundaryIntegral n φ hφ hgap R hi ho (fun z : ℂ => z⁻¹) hq
    have hcont : (∮ z in C(C.discs.center n,R), z⁻¹*sourceFullAbelianPrimitive hp hp1 W n (z,φ.val))=
        ∮ z in C(C.discs.center n,R), sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)/z := by
      apply circleIntegral.integral_congr hR
      intro z _
      dsimp only
      ring
    rw [hcont] at hw
    rw [hw]
    have he : (∫ θ in (0:ℝ)..Real.pi,
        (sourceStandardRootMidpoint hp hp1 φ.val n+sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ))⁻¹ *
        ((sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ:ℂ))*C.gapBoundary n φ.val θ true))=
        sourceStandardRootHalfGap hp hp1 φ.val n * ∫ θ in (0:ℝ)..Real.pi,
          (((realGapAffinePoint hp hp1 φ.val n (Real.cos θ))⁻¹ *
            (Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ):ℝ):ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le Real.pi_pos.le] at hθ
      dsimp only
      rw [C.gapBoundary_eq_realCosineProfile n φ hφ hgap θ hθ]
      have hx := sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint hp hp1 φ.val φ.property n (Real.cos θ)
      change sourceStandardRootMidpoint hp hp1 φ.val n+sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ)=_ at hx
      rw [hx]
      simp only [ofReal_mul,ofReal_inv]
      ring
    rw [he,intervalIntegral.integral_ofReal,
      sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 φ.val φ.property n]
    simp only [sourceRealInverseAction,ofReal_mul,ofReal_div,ofReal_sub,ofReal_ofNat,canonicalPeriodicGap,sub_re]
    ring

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
