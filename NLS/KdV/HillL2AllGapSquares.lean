import NLS.KdV.HillL2RealCutDifferential
import NLS.KdV.HillRealGapContours
import NLS.ComplexAnalysis.CoshSquareLocalCoordinate

/-! # Actual shifted squares through every closed real Hill gap

The two boundary signs disappear after squaring. Continuity and the
locally invertible squared-cosh coordinate recover analyticity at every
point of a closed gap, including endpoints and collisions. This fills
the actual square on the entire intrinsic isolating disc without a
high-index cutoff or a lower bound on the gap length.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV
open NLS.ComplexAnalysis

def hillL2RealGapPrimitiveSquare (q : Coeff 2) (n : ℕ) (z : ℂ) : ℂ :=
  (hillL2RealCutPrimitive q z + I * (n : ℂ) * Real.pi) ^ 2

theorem hillL2RealGapPrimitiveSquare_cosh
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ) :
    coshSquareCoordinate (hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) n z) =
      (-1 : ℂ) ^ n * hillL2Discriminant (SpectralWeight.one.toCoeff q) z / 2 := by
  rw [hillL2RealGapPrimitiveSquare, coshSquareCoordinate_sq, cosh_add_I_nat_pi,
    ← hillL2RealCutPrimitive_trace q hq hr z]
  ring

theorem hillL2RealGapPrimitiveSquare_on_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :
    hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) n x =
      (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) ^ 2 := by
  simp only [hillL2RealGapPrimitiveSquare, hillL2RealCutPrimitive, ofReal_im, if_true, ofReal_re]
  rw [hillL2UpperBoundaryPrimitive_gap_indexed q hq hr n hn x hx, sub_add_cancel]

theorem continuousAt_hillL2RealGapPrimitiveSquare_on_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :
    ContinuousAt (hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) n) (x : ℂ) := by
  let F : ℂ → ℂ := fun z => (hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q) + I * (n : ℂ) * Real.pi) ^ 2
  let B : ℝ → ℂ := fun y => (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) y + I * (n : ℂ) * Real.pi) ^ 2
  have hB : Continuous B := ((continuous_hillL2UpperBoundaryPrimitive q hq hr).add continuous_const).pow 2
  have hxB : B x = (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) ^ 2 := by
    dsimp only [B]
    rw [hillL2UpperBoundaryPrimitive_gap_indexed q hq hr n hn x hx, sub_add_cancel]
  have hu : Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (B x)) := by
    have ht := ((tendsto_hillL2ContinuedPrimitive_gap_upper q hq hr n hn x hx).add_const
      (I * (n : ℂ) * Real.pi)).pow 2
    simpa only [F, sub_add_cancel, hxB] using ht
  have hl : Tendsto F (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (B x)) := by
    have ht := ((tendsto_hillL2ContinuedPrimitive_gap_lower q hq hr n hn x hx).add_const
      (I * (n : ℂ) * Real.pi)).pow 2
    simpa only [F, sub_add_cancel, neg_sq, hxB] using ht
  have he : realBoundaryExtension F B = hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) n := by
    funext z
    by_cases hz : z.im = 0 <;> simp only [realBoundaryExtension, hillL2RealGapPrimitiveSquare,
      hillL2RealCutPrimitive, F, B, hz, if_true, if_false]
  rw [← he]
  exact continuousAt_realBoundaryExtension_of_limits F B x hB.continuousAt hu hl

theorem analyticAt_hillL2RealGapPrimitiveSquare_on_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :
    AnalyticAt ℂ (hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) n) (x : ℂ) := by
  apply analyticAt_of_continuousAt_coordinate coshSquareCoordinate
    (hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) n) x
    (analyticOnNhd_coshSquareCoordinate _ (mem_univ _))
  · rw [hillL2RealGapPrimitiveSquare_on_gap q hq hr n hn x hx]
    exact deriv_coshSquareCoordinate_sq_ne_zero _ (hillRealGapProfile_nonneg q hq hr n hn x hx)
  · exact continuousAt_hillL2RealGapPrimitiveSquare_on_gap q hq hr n hn x hx
  · have he : coshSquareCoordinate ∘ hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) n =
        (fun z => (-1 : ℂ) ^ n * hillL2Discriminant (SpectralWeight.one.toCoeff q) z / 2) :=
      funext (hillL2RealGapPrimitiveSquare_cosh q hq hr n)
    rw [he]
    exact (analyticAt_const.mul (analyticOnNhd_hillL2Discriminant _ x (mem_univ _))).div_const

theorem analyticOnNhd_hillL2RealGapPrimitiveSquare
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) n)
      (ball (hillRealGapCenter q hq hr n : ℂ)
        (hillRealGapHalfLength q hq hr n + 2 * hillRealGapCollar q hq hr n)) := by
  obtain ⟨_, _, _, _, hsub⟩ := hillRealGapContour_geometry q hq hr n hn
  intro z hz
  by_cases hk : z ∈ segment ℝ (hillRealLabels q hq hr (2 * n - 1) : ℂ) (hillRealLabels q hq hr (2 * n))
  · have hab := monotone_hillRealLabels q hq hr (show 2 * n - 1 ≤ 2 * n by omega)
    have hx := re_mem_Icc_of_mem_real_segment _ _ hab z hk
    have hi := im_eq_zero_of_mem_real_segment _ _ z hk
    have hzC : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    rw [hzC]
    exact analyticAt_hillL2RealGapPrimitiveSquare_on_gap q hq hr n hn z.re hx
  · exact (((analyticOnNhd_hillL2RealCutPrimitive q hq hr) z (hsub ⟨hz, hk⟩)).add analyticAt_const).pow 2

end NLS.KdV
