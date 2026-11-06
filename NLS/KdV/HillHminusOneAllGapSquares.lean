import NLS.KdV.HillHminusOneBandContinuation
import NLS.KdV.HillHminusOneGlobalGapBoundaryValues
import NLS.KdV.HillHminusOneRealGapContours
import NLS.ComplexAnalysis.CoshSquareLocalCoordinate

/-! # Actual shifted squares through every closed real Hill gap

The two boundary signs disappear after squaring. Continuity and the
locally invertible squared-cosh coordinate recover analyticity at every
point of a closed gap, including endpoints and collisions. This fills
the actual square on the entire intrinsic isolating disc without a
high-index cutoff or a lower bound on the gap length.
-/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV
open NLS.ComplexAnalysis

/-- The glued actual primitive retains its trace also on the closed gaps. -/
theorem hillHminusRealCutPrimitive_trace_all
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (z : ℂ) :
    2 * cosh (hillHminusRealCutPrimitive q z) = hillHminusDiscriminant q z := by
  by_cases hi : z.im = 0
  · have hzC : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    simpa only [hillHminusRealCutPrimitive, if_pos hi, ← hzC] using
      (hillHminusUpperBoundary_trace_all q hr z.re).1
  · simpa only [hillHminusRealCutPrimitive, if_neg hi] using
      (hillHminusContinuedPrimitive_trace _
        (mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hi)).1

def hillHminusRealGapPrimitiveSquare (q : PeriodOneHminusOne) (n : ℕ) (z : ℂ) : ℂ :=
  (hillHminusRealCutPrimitive q z + I * (n : ℂ) * Real.pi) ^ 2

theorem hillHminusRealGapPrimitiveSquare_cosh
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (z : ℂ) :
    coshSquareCoordinate (hillHminusRealGapPrimitiveSquare q n z) =
      (-1 : ℂ) ^ n * hillHminusDiscriminant q z / 2 := by
  rw [hillHminusRealGapPrimitiveSquare, coshSquareCoordinate_sq, cosh_add_I_nat_pi,
    ← hillHminusRealCutPrimitive_trace_all q hr z]
  ring

theorem hillHminusRealGapPrimitiveSquare_on_gap
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillHminusRealLabels q hr (2 * n - 1)) (hillHminusRealLabels q hr (2 * n))) :
    hillHminusRealGapPrimitiveSquare q n x =
      (hillHminusRealGapProfile q n x : ℂ) ^ 2 := by
  simp only [hillHminusRealGapPrimitiveSquare, hillHminusRealCutPrimitive, ofReal_im, if_true, ofReal_re]
  rw [hillHminusUpperBoundaryPrimitive_gap_indexed q hr n hn x hx, sub_add_cancel]

theorem continuousAt_hillHminusRealGapPrimitiveSquare_on_gap
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillHminusRealLabels q hr (2 * n - 1)) (hillHminusRealLabels q hr (2 * n))) :
    ContinuousAt (hillHminusRealGapPrimitiveSquare q n) (x : ℂ) := by
  let F : ℂ → ℂ := fun z => (hillHminusContinuedPrimitive (z, q) + I * (n : ℂ) * Real.pi) ^ 2
  let B : ℝ → ℂ := fun y => (hillHminusUpperBoundaryPrimitive q y + I * (n : ℂ) * Real.pi) ^ 2
  have hB : Continuous B := ((continuous_hillHminusUpperBoundaryPrimitive q hr).add continuous_const).pow 2
  have hxB : B x = (hillHminusRealGapProfile q n x : ℂ) ^ 2 := by
    dsimp only [B]
    rw [hillHminusUpperBoundaryPrimitive_gap_indexed q hr n hn x hx, sub_add_cancel]
  have hu : Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (B x)) := by
    have ht := ((tendsto_hillHminusContinuedPrimitive_gap_upper q hr n hn x hx).add_const
      (I * (n : ℂ) * Real.pi)).pow 2
    simpa only [F, sub_add_cancel, hxB] using ht
  have hl : Tendsto F (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (B x)) := by
    have ht := ((tendsto_hillHminusContinuedPrimitive_gap_lower q hr n hn x hx).add_const
      (I * (n : ℂ) * Real.pi)).pow 2
    simpa only [F, sub_add_cancel, neg_sq, hxB] using ht
  have he : realBoundaryExtension F B = hillHminusRealGapPrimitiveSquare q n := by
    funext z
    by_cases hz : z.im = 0 <;> simp only [realBoundaryExtension, hillHminusRealGapPrimitiveSquare,
      hillHminusRealCutPrimitive, F, B, hz, if_true, if_false]
  rw [← he]
  exact continuousAt_realBoundaryExtension_of_limits F B x hB.continuousAt hu hl

theorem analyticAt_hillHminusRealGapPrimitiveSquare_on_gap
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillHminusRealLabels q hr (2 * n - 1)) (hillHminusRealLabels q hr (2 * n))) :
    AnalyticAt ℂ (hillHminusRealGapPrimitiveSquare q n) (x : ℂ) := by
  apply analyticAt_of_continuousAt_coordinate coshSquareCoordinate
    (hillHminusRealGapPrimitiveSquare q n) x
    (analyticOnNhd_coshSquareCoordinate _ (mem_univ _))
  · rw [hillHminusRealGapPrimitiveSquare_on_gap q hr n hn x hx]
    exact deriv_coshSquareCoordinate_sq_ne_zero _ (hillHminusRealGapProfile_nonneg q hr n hn x hx)
  · exact continuousAt_hillHminusRealGapPrimitiveSquare_on_gap q hr n hn x hx
  · have he : coshSquareCoordinate ∘ hillHminusRealGapPrimitiveSquare q n =
        (fun z => (-1 : ℂ) ^ n * hillHminusDiscriminant q z / 2) :=
      funext (hillHminusRealGapPrimitiveSquare_cosh q hr n)
    rw [he]
    exact (analyticAt_const.mul (analyticOnNhd_hillHminusDiscriminant _ x (mem_univ _))).div_const

theorem analyticOnNhd_hillHminusRealGapPrimitiveSquare
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (hillHminusRealGapPrimitiveSquare q n)
      (ball (hillHminusRealGapCenter q hr n : ℂ)
        (hillHminusRealGapHalfLength q hr n + 2 * hillHminusRealGapCollar q hr n)) := by
  obtain ⟨_, _, _, _, hsub⟩ := hillHminusRealGapContour_geometry q hr n hn
  intro z hz
  by_cases hk : z ∈ segment ℝ (hillHminusRealLabels q hr (2 * n - 1) : ℂ) (hillHminusRealLabels q hr (2 * n))
  · have hab := monotone_hillHminusRealLabels q hr (show 2 * n - 1 ≤ 2 * n by omega)
    have hx := re_mem_Icc_of_mem_real_segment _ _ hab z hk
    have hi := im_eq_zero_of_mem_real_segment _ _ z hk
    have hzC : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    rw [hzC]
    exact analyticAt_hillHminusRealGapPrimitiveSquare_on_gap q hr n hn z.re hx
  · exact (((analyticOnNhd_hillHminusRealCutPrimitive q hr) z (hsub ⟨hz, hk⟩)).add analyticAt_const).pow 2

end NLS.KdV
