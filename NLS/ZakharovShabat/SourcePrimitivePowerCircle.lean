import NLS.ZakharovShabat.SourceAbelianMomentCircleVanishing
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! # Primitive-power moments on fixed circles

Section 21 uses `-1/pi` times the contour integral of the normalized
primitive raised to a natural power. These are different from the
psi-weighted moments of Section 20.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The fixed-contour version of `R_n^(m)` from Section 21. -/
def sourcePrimitivePowerCircle (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ) (m : ℕ) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) : ℂ :=
  -(Real.pi : ℂ)⁻¹ * ∮ z in C(c,R), (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^m

/-- Analyticity on an open source region with one admissible fixed circle. -/
theorem sourcePrimitivePowerCircle_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W U : Set (CoeffPair p)) (n : ℤ) (m : ℕ)
    (hU : IsOpen U) (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 U))
    (hF : AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W n)
      (sourceCanonicalRootJointDomain hp hp1 U))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ ψ ∈ U, sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    AnalyticOnNhd ℂ (fun ψ => sourcePrimitivePowerCircle hp hp1 W n m ψ c R) U := by
  have hi := analyticOnNhd_circleIntegral_of_jointAnalytic
    (fun t => (sourceFullAbelianPrimitive hp hp1 W n t)^m) hD
    (fun t ht => (hF t ht).pow m) c R hR hU
    (fun ψ hψ z hz => ⟨hψ,hc ψ hψ hz⟩)
  exact fun ψ hψ => analyticAt_const.mul (hi ψ hψ)

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

private theorem powerCircle_zero_of_extension
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) (m : ℕ)
    (ψ : CoeffPair p) (R : ℝ) (hR : 0 ≤ R) (houter : R < C.discs.outer n)
    (H : ℂ → ℂ) (hH : AnalyticOnNhd ℂ H (ball (C.discs.center n) (C.discs.outer n)))
    (he : ∀ z ∈ sphere (C.discs.center n) R,
      (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^m = H z) :
    sourcePrimitivePowerCircle hp hp1 W n m ψ (C.discs.center n) R = 0 := by
  have hd : DifferentiableOn ℂ H (closedBall (C.discs.center n) R) :=
    fun z hz => (hH z (closedBall_subset_ball houter hz)).differentiableAt.differentiableWithinAt
  have hzero := (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn).circleIntegral_eq_zero hR
  unfold sourcePrimitivePowerCircle
  rw [circleIntegral.integral_congr hR he,hzero,mul_zero]

/-- Lemma 21.1(ii), including the zeroth moment, on every intermediate circle. -/
theorem powerCircle_even_eq_zero
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) (m : ℕ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n) :
    sourcePrimitivePowerCircle hp hp1 W n (2*m) ψ (C.discs.center n) R = 0 := by
  apply C.powerCircle_zero_of_extension n (2*m) ψ R
    ((C.discs.inner_pos n).le.trans hinner) houter (fun z => (C.square n (z,ψ))^m)
    (fun z hz => (C.square_analytic n ψ hψ z hz).pow m)
  intro z hz
  rw [pow_mul,C.square_eq_fullPrimitive_sq n ψ hψ z
    ⟨closedBall_subset_ball houter (sphere_subset_closedBall hz),
      C.intermediate_circle_root n ψ hψ R hinner houter z hz n⟩]

/-- The collapsed-gap consequence of Lemma 21.1(iii), for every order. -/
theorem powerCircle_eq_zero_of_collapsed
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) (m : ℕ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n) :
    sourcePrimitivePowerCircle hp hp1 W n m ψ (C.discs.center n) R = 0 := by
  let Q : ℂ → ℂ := fun z => sourceFullAbelianCauchyQuotient hp hp1 W n
    (C.discs.center n) (C.discs.outer n) (z,ψ)
  apply C.powerCircle_zero_of_extension n m ψ R
    ((C.discs.inner_pos n).le.trans hinner) houter
    (fun z => ((sourceStandardRootMidpoint hp hp1 ψ n-z)*Q z)^m)
    (fun z hz => ((analyticAt_const.sub analyticAt_id).mul
      (C.quotient_slice_analytic n ψ hψ z hz)).pow m)
  intro z hz
  rw [C.fullPrimitive_eq_cauchy n n ψ hψ z
    ⟨closedBall_subset_ball houter (sphere_subset_closedBall hz),
      C.intermediate_circle_root n ψ hψ R hinner houter z hz n⟩]
  simp only [sub_self,mul_zero,add_zero,sourceFullAbelianCauchyPrimitive,
    sourceStandardRoot_of_zeroGap hp hp1 ψ n z hgap,sourceStandardRootMidpoint,Q]

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
