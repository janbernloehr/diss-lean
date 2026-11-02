import NLS.ZakharovShabat.SourceWeightedPrimitiveContour
import NLS.ComplexAnalysis.PiecewiseContourCongruence
import NLS.ComplexAnalysis.PiecewiseContourPeriod

/-! # The source NLS action contours at every integer level

Level k has the literal weight z^(k-1). On a zero-excluding isolating
circle the global ground-normalized primitive and the local gap-normalized
primitive have the same weighted contour. This includes level zero.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceLaurentActionContour (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (k : ℤ) (Γ : PiecewiseC1Loop) : ℂ :=
  -(Real.pi : ℂ)⁻¹ * Γ.integral (fun z => z^(k-1)*sourceAbelianPrimitive hp hp1 φ.val φ.property z)

def sourceLaurentPrimitiveCircle (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (n k : ℤ) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) : ℂ :=
  sourceWeightedPrimitiveCircle hp hp1 W n ψ c R (fun z => z^(k-1))

theorem sourceLaurentActionContour_circle_eq_local
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (n k : ℤ)
    (φ : realTypeSourceSubmodule p) (E : SourceAbelianSpectralChart hp hp1 W φ.val)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ.val)
    (hzero : (0 : ℂ) ∉ closedBall c R) :
    sourceLaurentActionContour hp hp1 φ k (PiecewiseC1Loop.circle c R) =
      sourceLaurentPrimitiveCircle hp hp1 W n k φ.val c R := by
  let w : ℂ → ℂ := fun z => z^(k-1)
  have hw : AnalyticOnNhd ℂ w (closedBall c R) := by
    intro z hz
    have hn : z ≠ 0 := by intro he; exact hzero (he ▸ hz)
    exact analyticAt_id.zpow hn
  have hd := hw.differentiableOn
  have hwzero := (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn).circleIntegral_eq_zero hR
  have hF : CircleIntegrable (fun z => w z*sourceAbelianPrimitive hp hp1 φ.val φ.property z) c R := by
    apply ContinuousOn.circleIntegrable hR
    intro z hz
    exact ((hw z (sphere_subset_closedBall hz)).continuousAt.mul
      (sourceAbelianPrimitive_analyticAt_of_mem_rootDomain hp hp1 φ.val φ.property z
        (hcircle hz)).continuousAt).continuousWithinAt
  have hconst : CircleIntegrable (fun z => (I*(Real.pi : ℂ)*n)*w z) c R :=
    ContinuousOn.circleIntegrable hR (continuousOn_const.mul (hw.continuousOn.mono sphere_subset_closedBall))
  have hi : (∮ z in C(c,R), w z*sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)) =
      ∮ z in C(c,R), w z*sourceAbelianPrimitive hp hp1 φ.val φ.property z+(I*(Real.pi : ℂ)*n)*w z := by
    apply circleIntegral.integral_congr hR
    intro z hz
    dsimp only
    rw [sourceFullAbelianPrimitive_eq_real φ E n z
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val (hcircle hz))]
    ring
  rw [sourceLaurentActionContour,PiecewiseC1Loop.integral_circle,sourceLaurentPrimitiveCircle,
    sourceWeightedPrimitiveCircle]
  change -(Real.pi : ℂ)⁻¹*(∮ z in C(c,R), w z*sourceAbelianPrimitive hp hp1 φ.val φ.property z) = _
  rw [hi,circleIntegral.integral_add hF hconst,circleIntegral.integral_const_mul,hwzero,mul_zero,add_zero]

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The real-gap formula for every Laurent level on an actual
zero-excluding disc, including collapsed gaps. -/
theorem laurentPrimitiveCircle_eq_realIntegral
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n k : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n)
    (hzero : (0 : ℂ) ∉ closedBall (C.discs.center n) R) :
    sourceLaurentPrimitiveCircle hp hp1 W n k φ.val (C.discs.center n) R =
      (((canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re /
        Real.pi * ∫ θ in (0 : ℝ)..Real.pi,
          (realGapAffinePoint hp hp1 φ.val n (Real.cos θ))^(k-1) *
            (Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ) : ℝ) : ℂ) := by
  have hw : AnalyticOnNhd ℂ (fun z : ℂ => z^(k-1)) (closedBall (C.discs.center n) R) := by
    intro z hz
    exact analyticAt_id.zpow (by intro he; exact hzero (he ▸ hz))
  rw [sourceLaurentPrimitiveCircle,C.weightedPrimitiveCircle_eq_realIntegral n φ hφ R hinner houter _ hw]
  simp only [← ofReal_zpow,← ofReal_mul,← ofReal_div]
  rw [intervalIntegral.integral_ofReal,ofReal_mul]

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
