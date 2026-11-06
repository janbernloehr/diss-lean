import NLS.KdV.HillFreeTraceContour
import NLS.KdV.ActionHamiltonianTrace

/-! # Exact quartic source-primitive periods and physical gap contributions -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV
open NLS.ComplexAnalysis

def hillL2FreeQuarticPeriod (q : Coeff 2) (N : ℕ) : ℂ :=
  (-4 : ℂ)*(2*Real.pi*I : ℂ)⁻¹ *
    ∮ w in C(0,(hillFreeBandFrequency N)^2), hillL2RealCutPrimitive q w ^ 4

def hillL2RealCubicContourMoment
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) : ℂ :=
  cubicMoment (fun z => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z+I*(n : ℂ)*Real.pi)
    (hillRealGapCenter q hq hr n : ℂ)
    (hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n)

theorem sphere_subset_hillFree_holeDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (hN : 2 ≤ N)
    (hcut : 8*‖q‖ ≤ (N : ℝ))
    (hground : -(hillFreeBandFrequency N)^2 < hillLowestEnergy q hq hr) : sphere (0 : ℂ) ((hillFreeBandFrequency N)^2) ⊆
      circleHoleDomain 0 ((hillFreeBandFrequency N)^2) (Finset.Icc 1 N)
        (fun n => (hillRealGapCenter q hq hr n : ℂ))
        (fun n => hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n) := by
    intro w hw
    refine ⟨sphere_subset_closedBall hw, ?_⟩
    intro n hn hball
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnN := (Finset.mem_Icc.mp hn).2
    have hbig : w ∈ closedBall (hillRealGapCenter q hq hr n : ℂ) (hillRealGapOuterRadius q hq hr n) :=
      (closedBall_subset_closedBall (hillRealGapOuterRadius_bounds q hq hr n hn1).2.1.le)
        (ball_subset_closedBall hball)
    exact sphere_disjoint_ball.le_bot ⟨hw,
      hillRealGapOuter_enclosed_free q hq hr N hN hcut hground n hn1 hnN hbig⟩

theorem analyticOnNhd_hillFree_perforated_quartic
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (hN : 2 ≤ N)
    (hcut : 8*‖q‖ ≤ (N : ℝ)) :
    AnalyticOnNhd ℂ (fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 4)
      (circleHoleDomain 0 ((hillFreeBandFrequency N)^2) (Finset.Icc 1 N)
        (fun n => (hillRealGapCenter q hq hr n : ℂ))
        (fun n => hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n)) := by
  have hh := (analyticOnNhd_hillFree_perforated_square q hq hr N hN hcut 0).pow 2
  have he : (fun w : ℂ => w^0*hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w^2)^2 =
      (fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w^4) := by
    funext w
    simp only [Pi.pow_apply,pow_zero,one_mul,←pow_mul]
  rw [he] at hh
  exact hh

theorem circleIntegrable_hillL2FreeQuarticIntegrand
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (hN : 2 ≤ N)
    (hcut : 8*‖q‖ ≤ (N : ℝ))
    (hground : -(hillFreeBandFrequency N)^2 < hillLowestEnergy q hq hr) :
    CircleIntegrable (fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 4)
      0 ((hillFreeBandFrequency N)^2) :=
  ((analyticOnNhd_hillFree_perforated_quartic q hq hr N hN hcut).continuousOn.mono
    (sphere_subset_hillFree_holeDomain q hq hr N hN hcut hground)).circleIntegrable (sq_nonneg _)

theorem hillL2QuarticGapPeriod_eq_action_and_cubic
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    (-4 : ℂ)*(2*Real.pi*I : ℂ)⁻¹ *
      (∮ z in C((hillRealGapCenter q hq hr n : ℂ),
        hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n),
        hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ 4) =
      ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*hillL2RealContourMoment q hq hr n 0+
        ((8*(n : ℝ)*Real.pi : ℝ) : ℂ)*hillL2RealCubicContourMoment q hq hr n := by
  let c := (hillRealGapCenter q hq hr n : ℂ)
  let r := hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n
  let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)
  obtain ⟨hd,hη,_⟩ := hillRealGapContour_geometry q hq hr n hn
  have hrad : 0 ≤ r := by dsimp [r];linarith
  have hs := hillRealGapContour_sphere_subset q hq hr n hn
  have hcont : ContinuousOn (fun z => F z+I*(n : ℂ)*Real.pi) (sphere c r) :=
    ((analyticOnNhd_hillL2RealCutPrimitive q hq hr).continuousOn.mono hs).add_const _
  have hsq : AnalyticOnNhd ℂ (fun z => (F z+I*(n : ℂ)*Real.pi)^2) (closedBall c r) :=
    (analyticOnNhd_hillL2RealGapPrimitiveSquare q hq hr n hn).mono
      (closedBall_subset_ball (by dsimp [r];linarith))
  have haction : primitiveAction (fun z => F z+I*(n : ℂ)*Real.pi) c r =
      hillL2RealContourMoment q hq hr n 0 := by
    rw [primitiveAction_add_const_of_analyticOnNhd F (hillL2RealCutDomain q hq hr)
      (analyticOnNhd_hillL2RealCutPrimitive q hq hr) c _ r hrad hs]
    simp only [primitiveAction,hillL2RealContourMoment,pow_zero,one_mul]
    rfl
  have hh := quartic_gap_contribution (fun z => F z+I*(n : ℂ)*Real.pi) c r (n : ℝ) hrad hcont hsq
  simpa only [ofReal_natCast,add_sub_cancel_right,haction,hillL2RealCubicContourMoment] using! hh

theorem hillL2FreeQuarticPeriod_eq_partial_moments
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (hN : 2 ≤ N)
    (hcut : 8*‖q‖ ≤ (N : ℝ))
    (hground : -(hillFreeBandFrequency N)^2 < hillLowestEnergy q hq hr) :
    hillL2FreeQuarticPeriod (SpectralWeight.one.toCoeff q) N =
      ∑ n ∈ Finset.Icc 1 N,
        (((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*hillL2RealContourMoment q hq hr n 0+
        ((8*(n : ℝ)*Real.pi : ℝ) : ℂ)*hillL2RealCubicContourMoment q hq hr n) := by
  have hdecomp : (∮ w in C((0 : ℂ), (hillFreeBandFrequency N)^2),
      hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 4) =
      ∑ n ∈ Finset.Icc 1 N, ∮ w in C((hillRealGapCenter q hq hr n : ℂ),
          hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n),
        hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 4 := by
    apply circleIntegral_eq_sum_of_finite_holes _ _ (sq_nonneg _) (Finset.Icc 1 N)
      (fun n => (hillRealGapCenter q hq hr n : ℂ))
      (fun n => hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n)
      (hillRealGapOuterRadius q hq hr)
    · intro n hn
      exact (hillRealGapOuterRadius_bounds q hq hr n (Finset.mem_Icc.mp hn).1).1
    · intro n hn
      exact (hillRealGapOuterRadius_bounds q hq hr n (Finset.mem_Icc.mp hn).1).2.1
    · intro n hn
      exact hillRealGapOuter_enclosed_free q hq hr N hN hcut hground n
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
    · intro i hi j hj hij
      exact hillRealGapOuter_disjoint q hq hr i j (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1 hij
    · exact analyticOnNhd_hillFree_perforated_quartic q hq hr N hN hcut
  rw [hillL2FreeQuarticPeriod, hdecomp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact hillL2QuarticGapPeriod_eq_action_and_cubic q hq hr n (Finset.mem_Icc.mp hn).1


end NLS.KdV
