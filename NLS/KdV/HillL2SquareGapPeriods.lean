import NLS.KdV.HillL2AllGapSquares
import NLS.KdV.HillL2RealContourMoments
import NLS.ComplexAnalysis.ShiftedSquarePeriod

/-! # The exact squared-primitive gap terms in the Hill trace formula

The filled shifted square kills the even gap term. The remaining
linear term is exactly `(2*n*pi) * J_(n,m)` with the source orientation
and normalization, at every gap and integer level. Physical exterior
Laurent coefficients and infinite contour sums remain separate.
-/

noncomputable section
open Set Metric Complex Filter Topology MeasureTheory
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem circleIntegral_hillL2ShiftedSquare_eq_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    (∮ z in C((hillRealGapCenter q hq hr n : ℂ),
        hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n),
      z ^ m * hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) n z) = 0 := by
  obtain ⟨hd, hη, _⟩ := hillRealGapContour_geometry q hq hr n hn
  have hrad : 0 ≤ hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n := by linarith
  have hsub : closedBall (hillRealGapCenter q hq hr n : ℂ)
      (hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n) ⊆
      ball (hillRealGapCenter q hq hr n : ℂ)
        (hillRealGapHalfLength q hq hr n + 2 * hillRealGapCollar q hq hr n) :=
    closedBall_subset_ball (by linarith :
    hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n <
      hillRealGapHalfLength q hq hr n + 2 * hillRealGapCollar q hq hr n)
  have ha := (analyticOnNhd_id.pow m).mul
    ((analyticOnNhd_hillL2RealGapPrimitiveSquare q hq hr n hn).mono hsub)
  exact circleIntegral_eq_zero_of_differentiable_on_off_countable hrad countable_empty
    ha.continuousOn (fun z hz => (ha z (ball_subset_closedBall hz.1)).differentiableAt)

theorem hillL2SquareGapPeriod_eq_weightedMoment
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    ((Real.pi : ℂ) * I)⁻¹ *
      (∮ z in C((hillRealGapCenter q hq hr n : ℂ),
          hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n),
        z ^ m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ 2) =
      (2 * (n : ℂ) * Real.pi) * hillL2RealContourMoment q hq hr n m := by
  let F : ℂ → ℂ := fun z => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z + I * (n : ℂ) * Real.pi
  let c := (hillRealGapCenter q hq hr n : ℂ)
  let r := hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n
  obtain ⟨hd, hη, _⟩ := hillRealGapContour_geometry q hq hr n hn
  have hrad : 0 ≤ r := by dsimp only [r]; linarith
  have hs := hillRealGapContour_sphere_subset q hq hr n hn
  have hF : ContinuousOn F (sphere c r) :=
    ((analyticOnNhd_hillL2RealCutPrimitive q hq hr).continuousOn.mono hs).add_const _
  have hSq : AnalyticOnNhd ℂ (fun z => F z ^ 2) (closedBall c r) :=
    (analyticOnNhd_hillL2RealGapPrimitiveSquare q hq hr n hn).mono
      (closedBall_subset_ball (by dsimp only [r]; linarith))
  have he := circleIntegral_pow_mul_shifted_square F (I * (n : ℂ) * Real.pi) c r hrad hF hSq m
  simp only [F, add_sub_cancel_right] at he
  rw [circleIntegral_hillL2RealCutPrimitive_shifted q hq hr n hn m] at he
  rw [he, hillL2RealContourMoment_eq_gapIntegral q hq hr n hn]
  unfold hillRealGapIntegral
  simp_rw [← ofReal_pow, ← ofReal_mul]
  rw [intervalIntegral.integral_ofReal]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hpi, I_ne_zero]

end NLS.KdV
