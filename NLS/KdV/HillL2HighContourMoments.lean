import NLS.KdV.HillL2SourcePrimitive
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher
import NLS.ComplexAnalysis.CircleIntegralIntegrationByParts

/-! # Analytic high contour moments of the actual L2 Hill primitive

These fixed-circle functionals use the source-normalized physical trace.
They are analytic near every checked high-index potential, vanish at the
free potential, and at level zero satisfy the actual Arnold contour
formula. Identification with globally defined canonical actions, contour
independence, positivity and quantitative action bounds are not asserted.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

/-- The source-normalized moment on the explicit high energy circle.
Its physical interpretation is asserted only where the contour lies in
the checked continuation domain. -/
def hillL2HighContourMoment (n m : ℕ) (q : Coeff 2) : ℂ :=
  -(Real.pi : ℂ)⁻¹ * ∮ z in C((freeHillValue n : ℂ),(n : ℝ)),
    z^m*hillL2ContinuedPrimitive (z,q)

theorem analyticAt_hillL2HighContourMoment
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    AnalyticAt ℂ (hillL2HighContourMoment n m) (SpectralWeight.one.toCoeff q) := by
  obtain ⟨V,hV,hqV,hcircle⟩ := exists_hillL2Continuation_high_contour_neighborhood q hq n hn hcut
  let F : ℂ × Coeff 2 → ℂ := fun t => t.1^m*hillL2ContinuedPrimitive t
  have hF : AnalyticOnNhd ℂ F hillL2ContinuationDomain := by
    intro t ht
    exact (analyticAt_fst.pow m).mul (analyticOnNhd_hillL2ContinuedPrimitive t ht)
  have hraw := analyticOnNhd_circleIntegral_of_jointAnalytic F
    isOpen_hillL2ContinuationDomain hF (freeHillValue n : ℂ) (n : ℝ)
    (by positivity) hV (fun a ha z hz => hcircle ⟨hz,ha⟩)
  exact analyticAt_const.mul (hraw _ hqV)

@[simp] theorem hillL2HighContourMoment_zero (n m : ℕ) (hn : 1 ≤ n) :
    hillL2HighContourMoment n m 0 = 0 := by
  have ha : AnalyticOnNhd ℂ (fun z => z^m*classicalHillFreePrimitive z)
      (closedBall (freeHillValue n : ℂ) (n : ℝ)) := by
    intro z hz
    exact (analyticAt_id.pow m).mul
      (analyticOnNhd_classicalHillFreePrimitive z (hillClosedBall_subset_slitPlane n hn hz))
  have hzero := (DiffContOnCl.mk_ball
    (ha.differentiableOn.mono ball_subset_closedBall) ha.continuousOn).circleIntegral_eq_zero
    (show (0 : ℝ) ≤ n by positivity)
  simp only [hillL2HighContourMoment,hillL2ContinuedPrimitive_base,
    classicalHillFreePrimitive] at hzero ⊢
  rw [hzero,mul_zero]

/-- The primitive moment has exactly the source's level-zero Arnold
integrand and normalization on the whole checked high circle. -/
theorem hillL2HighContourMoment_arnold
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    hillL2HighContourMoment n 0 (SpectralWeight.one.toCoeff q) =
      (Real.pi : ℂ)⁻¹ * ∮ z in C((freeHillValue n : ℂ),(n : ℝ)),
        z*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
          hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q) := by
  let P : ℂ → ℂ := fun z => hillL2ContinuedPrimitive (z,SpectralWeight.one.toCoeff q)
  let D : Set ℂ := {z | (z,SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain}
  have hP : AnalyticOnNhd ℂ P D := by
    intro z hz
    exact (analyticOnNhd_hillL2ContinuedPrimitive _ hz).comp
      (f := fun z : ℂ => (z,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  have hcircle : sphere (freeHillValue n : ℂ) (n : ℝ) ⊆ D :=
    mem_hillL2ContinuationDomain_high_sphere q hq n hn hcut
  have hip := circleIntegral_mul_deriv_eq_neg_of_analyticOnNhd P D hP
    (freeHillValue n : ℂ) (n : ℝ) (by positivity) hcircle
  have hi : (∮ z in C((freeHillValue n : ℂ),(n : ℝ)),
      z*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
        hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q)) =
      -(∮ z in C((freeHillValue n : ℂ),(n : ℝ)), P z) := by
    rw [← hip]
    apply circleIntegral.integral_congr (by positivity)
    intro z hz
    dsimp only [P]
    rw [(hasDerivAt_hillL2ContinuedPrimitive _ (hcircle hz)).deriv]
    exact mul_div_assoc z _ _
  simp only [hillL2HighContourMoment,pow_zero,one_mul,hi,mul_neg,neg_mul,P]

end NLS.KdV
