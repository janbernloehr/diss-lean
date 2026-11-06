import NLS.KdV.HillOuterTraceGeometry
import NLS.ComplexAnalysis.FiniteCircleHoleDecomposition

/-! # The actual filled-square domain contains each finite perforated disc -/

noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.ComplexAnalysis

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
variable (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
variable (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem ofReal_mem_hillRealGap_inner_ball (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :
    (x : ℂ) ∈ ball (hillRealGapCenter q hq hr n : ℂ)
      (hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n) := by
  obtain ⟨_, hη, hl, hu, _⟩ := hillRealGapContour_geometry q hq hr n hn
  rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [hx.1, hx.2]

theorem hillRealOuter_closedBall_re_le (N : ℕ) (z : ℂ)
    (hz : z ∈ closedBall (hillRealOuterCenter q hq hr : ℂ) (hillRealOuterRadius q hq hr N)) :
    z.re ≤ hillRealOuterUpper q hq hr N := by
  have hd : ‖z - (hillRealOuterCenter q hq hr : ℂ)‖ ≤ hillRealOuterRadius q hq hr N := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hreal : |z.re - hillRealOuterCenter q hq hr| ≤ hillRealOuterRadius q hq hr N := by
    simpa only [sub_re, ofReal_re] using (abs_re_le_norm (z - (hillRealOuterCenter q hq hr : ℂ))).trans hd
  have hu := (abs_le.mp hreal).2
  dsimp [hillRealOuterRadius] at hu
  linarith

theorem hillRealOuter_holeDomain_subset (N : ℕ) :
    circleHoleDomain (hillRealOuterCenter q hq hr : ℂ) (hillRealOuterRadius q hq hr N)
      (Finset.Icc 1 N) (fun n => (hillRealGapCenter q hq hr n : ℂ))
      (fun n => hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n) ⊆
        hillL2FilledSquareDomain q hq hr := by
  intro z hz
  by_cases hi : z.im ≠ 0
  · exact Or.inl (Or.inl hi)
  by_cases hground : z.re ≤ hillLowestEnergy q hq hr
  · exact Or.inr (Or.inl hground)
  have hzC : z = (z.re : ℂ) := by apply Complex.ext <;> simp [not_ne_iff.mp hi]
  have hx0 : hillLowestEnergy q hq hr < z.re := not_le.mp hground
  have hxN : z.re < hillRealLabels q hq hr (2 * N + 1) :=
    (hillRealOuter_closedBall_re_le q hq hr N z hz.1).trans_lt (hillRealOuterUpper_mem_band q hq hr N).2
  have hgap (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
      z.re ∉ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n)) := by
    intro hmem
    apply hz.2 n (Finset.mem_Icc.mpr ⟨hn, hnN⟩)
    rw [hzC]
    exact ofReal_mem_hillRealGap_inner_ball q hq hr n hn z.re hmem
  obtain ⟨k, _, hband⟩ := hillRealLabels_finite_band_cover q hq hr N z.re hx0 hxN hgap
  exact Or.inl (Or.inr ⟨k, hband⟩)

theorem analyticOnNhd_hillRealOuter_perforated_square (N m : ℕ) :
    AnalyticOnNhd ℂ (fun z => z ^ m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ 2)
      (circleHoleDomain (hillRealOuterCenter q hq hr : ℂ) (hillRealOuterRadius q hq hr N)
        (Finset.Icc 1 N) (fun n => (hillRealGapCenter q hq hr n : ℂ))
        (fun n => hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n)) := by
  have hzero : hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) 0 =
      (fun z => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ 2) := by
    funext z
    simp only [hillL2RealGapPrimitiveSquare, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  have ha : AnalyticOnNhd ℂ (fun z => z ^ m * hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) 0 z)
      (circleHoleDomain (hillRealOuterCenter q hq hr : ℂ) (hillRealOuterRadius q hq hr N)
        (Finset.Icc 1 N) (fun n => (hillRealGapCenter q hq hr n : ℂ))
        (fun n => hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n)) :=
    (analyticOnNhd_id.pow m).mul
      ((analyticOnNhd_hillL2FilledSquare q hq hr).mono (hillRealOuter_holeDomain_subset q hq hr N))
  simpa only [hzero] using ha

end NLS.KdV
