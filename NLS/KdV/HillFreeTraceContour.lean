import NLS.KdV.HillFreeCircleGeometry
import NLS.KdV.HillOuterTraceDomain
import NLS.KdV.HillL2SquareGapPeriods
import NLS.KdV.HillFreeUpperArcs

/-! # Exact actual gap sums on the free half-lattice energy circles -/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV
open NLS.ComplexAnalysis

def hillL2FreeSquarePeriod (q : Coeff 2) (N m : ℕ) : ℂ :=
  ((Real.pi : ℂ)*I)⁻¹ * ∮ w in C((0 : ℂ), (hillFreeBandFrequency N)^2),
    w^m * hillL2RealCutPrimitive q w ^ 2

theorem hillFree_holeDomain_subset
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (hN : 2 ≤ N)
    (hcut : 8*‖q‖ ≤ (N : ℝ)) :
    circleHoleDomain 0 ((hillFreeBandFrequency N)^2) (Finset.Icc 1 N)
      (fun n => (hillRealGapCenter q hq hr n : ℂ))
      (fun n => hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n) ⊆
        hillL2FilledSquareDomain q hq hr := by
  intro z hz
  by_cases hi : z.im ≠ 0
  · exact Or.inl (Or.inl hi)
  by_cases hg : z.re ≤ hillLowestEnergy q hq hr
  · exact Or.inr (Or.inl hg)
  have hzC : z = (z.re : ℂ) := by apply Complex.ext <;> simp [not_ne_iff.mp hi]
  have hnorm : ‖z‖ ≤ (hillFreeBandFrequency N)^2 := by
    simpa only [mem_closedBall, dist_zero_right] using hz.1
  have hxN : z.re < hillRealLabels q hq hr (2*N+1) :=
    ((re_le_norm z).trans hnorm).trans_lt (hillFreeBandFrequency_sq_mem_band q hq hr N hN hcut).2
  have hgap (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
      z.re ∉ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) := by
    intro hx
    apply hz.2 n (Finset.mem_Icc.mpr ⟨hn, hnN⟩)
    rw [hzC]
    exact ofReal_mem_hillRealGap_inner_ball q hq hr n hn z.re hx
  obtain ⟨k, _, hk⟩ := hillRealLabels_finite_band_cover q hq hr N z.re (not_le.mp hg) hxN hgap
  exact Or.inl (Or.inr ⟨k, hk⟩)

theorem analyticOnNhd_hillFree_perforated_square
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (hN : 2 ≤ N)
    (hcut : 8*‖q‖ ≤ (N : ℝ)) (m : ℕ) :
    AnalyticOnNhd ℂ (fun w => w^m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 2)
      (circleHoleDomain 0 ((hillFreeBandFrequency N)^2) (Finset.Icc 1 N)
        (fun n => (hillRealGapCenter q hq hr n : ℂ))
        (fun n => hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n)) := by
  have hzero : hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) 0 =
      (fun z => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ 2) := by
    funext z
    simp only [hillL2RealGapPrimitiveSquare, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  have h : AnalyticOnNhd ℂ (fun w : ℂ => w^m * hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) 0 w)
      (circleHoleDomain 0 ((hillFreeBandFrequency N)^2) (Finset.Icc 1 N)
        (fun n => (hillRealGapCenter q hq hr n : ℂ))
        (fun n => hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n)) :=
    (analyticOnNhd_id.pow m).mul
    ((analyticOnNhd_hillL2FilledSquare q hq hr).mono (hillFree_holeDomain_subset q hq hr N hN hcut))
  simpa only [hzero] using h

theorem circleIntegrable_hillL2FreeSquareIntegrand
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (hN : 2 ≤ N)
    (hcut : 8*‖q‖ ≤ (N : ℝ))
    (hground : -(hillFreeBandFrequency N)^2 < hillLowestEnergy q hq hr) (m : ℕ) :
    CircleIntegrable (fun w => w^m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 2)
      0 ((hillFreeBandFrequency N)^2) := by
  have hcover : sphere (0 : ℂ) ((hillFreeBandFrequency N)^2) ⊆
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
  exact ((analyticOnNhd_hillFree_perforated_square q hq hr N hN hcut m).continuousOn.mono hcover).circleIntegrable (sq_nonneg _)

theorem hillL2FreeSquarePeriod_eq_partial_moments
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (hN : 2 ≤ N)
    (hcut : 8*‖q‖ ≤ (N : ℝ))
    (hground : -(hillFreeBandFrequency N)^2 < hillLowestEnergy q hq hr) (m : ℕ) :
    hillL2FreeSquarePeriod (SpectralWeight.one.toCoeff q) N m =
      ∑ n ∈ Finset.Icc 1 N, (2*(n : ℂ)*Real.pi) * hillL2RealContourMoment q hq hr n m := by
  have hdecomp : (∮ w in C((0 : ℂ), (hillFreeBandFrequency N)^2),
      w^m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 2) =
      ∑ n ∈ Finset.Icc 1 N, ∮ w in C((hillRealGapCenter q hq hr n : ℂ),
          hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n),
        w^m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 2 := by
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
    · exact analyticOnNhd_hillFree_perforated_square q hq hr N hN hcut m
  rw [hillL2FreeSquarePeriod, hdecomp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact hillL2SquareGapPeriod_eq_weightedMoment q hq hr n (Finset.mem_Icc.mp hn).1 m

theorem eventually_hillFreeCircle_conditions
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ 8*‖q‖ ≤ (N : ℝ) ∧
      -(hillFreeBandFrequency N)^2 < hillLowestEnergy q hq hr := by
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop (8*‖q‖),
    tendsto_hillFreeBandFrequency.eventually_ge_atTop (max 1 (1-hillLowestEnergy q hq hr))]
    with N hN hcut hg
  have h1 : 1 ≤ hillFreeBandFrequency N := (le_max_left _ _).trans hg
  have h2 : 1-hillLowestEnergy q hq hr ≤ hillFreeBandFrequency N := (le_max_right _ _).trans hg
  exact ⟨hN, hcut, by nlinarith⟩

theorem eventually_hillL2FreeSquarePeriod_eq_partial_moments
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ,
      hillL2FreeSquarePeriod (SpectralWeight.one.toCoeff q) N m =
        ∑ n ∈ Finset.Icc 1 N, (2*(n : ℂ)*Real.pi) * hillL2RealContourMoment q hq hr n m := by
  filter_upwards [eventually_hillFreeCircle_conditions q hq hr] with N hN
  intro m
  exact hillL2FreeSquarePeriod_eq_partial_moments q hq hr N hN.1 hN.2.1 hN.2.2 m

end NLS.KdV
