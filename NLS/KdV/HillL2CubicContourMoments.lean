import NLS.KdV.HillL2ContourDeformation

/-! # Cubic shifted-primitive moments in the L2 Hill realization

These are the literal cubic periods used for the renormalized KdV
Hamiltonian. Each checked high contour has an open L2 neighborhood of
analyticity. The annular source domain also gives contour independence.
No global Birkhoff action-space descent is asserted here.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

def hillL2HighCubicContourMoment (n : ℕ) (q : Coeff 2) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∮ z in C((freeHillValue n : ℂ),(n : ℝ)),
    (hillL2ContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi)^3

theorem analyticAt_hillL2HighCubicContourMoment
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    AnalyticAt ℂ (hillL2HighCubicContourMoment n) (SpectralWeight.one.toCoeff q) := by
  obtain ⟨V,hV,hqV,hcircle⟩ := exists_hillL2Continuation_high_contour_neighborhood q hq n hn hcut
  let F : ℂ × Coeff 2 → ℂ := fun t => (hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi)^3
  have hF : AnalyticOnNhd ℂ F hillL2ContinuationDomain :=
    (analyticOnNhd_hillL2ContinuedPrimitive.add analyticOnNhd_const).pow 3
  have hi := analyticOnNhd_circleIntegral_of_jointAnalytic F
    isOpen_hillL2ContinuationDomain hF (freeHillValue n : ℂ) (n : ℝ)
    (by positivity) hV (fun a ha z hz => hcircle ⟨hz,ha⟩)
  exact (hi _ hqV).const_smul (c := (Real.pi : ℂ)⁻¹)

theorem hillL2HighCubicContourMoment_eq_radius
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (r : ℝ) (hr : 4*‖q‖ < r) (hrn : r ≤ (n : ℝ)) :
    hillL2HighCubicContourMoment n (SpectralWeight.one.toCoeff q) =
      (Real.pi : ℂ)⁻¹ * ∮ z in C((freeHillValue n : ℂ),r),
        (hillL2ContinuedPrimitive (z,SpectralWeight.one.toCoeff q)+I*(n : ℂ)*Real.pi)^3 := by
  have hrpos : 0 < r := (by positivity : (0 : ℝ) ≤ 4*‖q‖).trans_lt hr
  have hF : AnalyticOnNhd ℂ
      (fun z => (hillL2ContinuedPrimitive (z,SpectralWeight.one.toCoeff q)+I*(n : ℂ)*Real.pi)^3)
      (closedBall (freeHillValue n : ℂ) (n : ℝ) \ ball (freeHillValue n : ℂ) r) := by
    intro z hz
    have hd := hillL2Continuation_high_annulus q hq n hn hcut r (n : ℝ) hr le_rfl z hz
    exact (((analyticOnNhd_hillL2ContinuedPrimitive _ hd).comp
      (f := fun z : ℂ => (z,SpectralWeight.one.toCoeff q))
      (analyticAt_id.prod analyticAt_const)).add analyticAt_const).pow 3
  have hi := circleIntegral_eq_of_differentiable_on_annulus_off_countable hrpos hrn
    countable_empty hF.continuousOn (fun z hz =>
      (hF z ⟨ball_subset_closedBall hz.1.1,
        fun h => hz.1.2 (ball_subset_closedBall h)⟩).differentiableAt)
  exact congrArg (fun a : ℂ => (Real.pi : ℂ)⁻¹*a) hi

@[simp] theorem hillL2HighCubicContourMoment_zero (n : ℕ) (hn : 1 ≤ n) :
    hillL2HighCubicContourMoment n 0 = 0 := by
  have hF : AnalyticOnNhd ℂ
      (fun z => (classicalHillFreePrimitive z+I*(n : ℂ)*Real.pi)^3)
      (closedBall (freeHillValue n : ℂ) (n : ℝ)) := by
    intro z hz
    exact ((analyticOnNhd_classicalHillFreePrimitive z
      (hillClosedBall_subset_slitPlane n hn hz)).add analyticAt_const).pow 3
  have hi := (DiffContOnCl.mk_ball
    (hF.differentiableOn.mono ball_subset_closedBall) hF.continuousOn).circleIntegral_eq_zero
    (show (0 : ℝ) ≤ n by positivity)
  simp only [hillL2HighCubicContourMoment,hillL2ContinuedPrimitive_base,
    classicalHillFreePrimitive] at hi ⊢
  rw [hi,mul_zero]

end NLS.KdV
