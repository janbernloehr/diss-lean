import NLS.KdV.HillL2EndpointContinuity

/-! # The actual squared primitive through the lowest spectral cut

The boundary phase below the lowest energy is fixed to zero by its
continuous endpoint value. The two primitive signs then disappear after
squaring, and the squared-cosh coordinate fills the lowest branch point
and the whole real ray below it analytically.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem hillL2UpperBoundaryPrimitive_ground
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) (hillLowestEnergy q hq hr) = 0 := by
  simpa only [hillLowestEnergy, show (0 + 1) / 2 = (0 : ℕ) by decide, Nat.cast_zero, mul_zero, zero_mul] using
    hillL2UpperBoundaryPrimitive_label_indexed q hq hr 0

theorem hillL2UpperBoundaryPrimitive_im_eq_zero_below
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ)
    (hx : x < hillLowestEnergy q hq hr) :
    (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).im = 0 := by
  have hreg (y : ℝ) (hy : y < hillLowestEnergy q hq hr) :
      hillL2Radicand (SpectralWeight.one.toCoeff q) y ≠ 0 := by
    intro he
    have hp := hillL2Radicand_pos_below q hq hr y hy
    simp only [he, zero_re, lt_self_iff_false] at hp
  let f : ℝ → ℝ := fun y => (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) y).im
  have hf : Continuous f := continuous_im.comp (continuous_hillL2UpperBoundaryPrimitive q hq hr)
  have hsin (y : ℝ) (hy : y ∈ Iio (hillLowestEnergy q hq hr)) : Real.sin (f y) = 0 := by
    have hd := hillL2Discriminant_gt_two_below q hq hr y hy
    have ht := re_eq_arcosh_of_real_cosh_trace_gap _ _
      (hillL2UpperBoundaryPrimitive_trace q hq hr y (hreg y hy))
      (hillL2UpperBoundaryPrimitive_re_nonneg q hq hr y (hreg y hy))
      (by rw [abs_of_pos (by linarith)]; exact hd)
    exact ht.2.2
  have he : EqOn f (fun _ => f x) (Iio (hillLowestEnergy q hq hr)) :=
    phase_eq_on_of_sin_eq_zero f _ isPreconnected_Iio hf.continuousOn hsin x hx
  have hclosure : hillLowestEnergy q hq hr ∈ closure (Iio (hillLowestEnergy q hq hr)) := by
    rw [closure_Iio (hillLowestEnergy q hq hr)]
    exact (le_rfl : hillLowestEnergy q hq hr ≤ hillLowestEnergy q hq hr)
  have hb := he.closure hf continuous_const hclosure
  simpa only [f, hillL2UpperBoundaryPrimitive_ground q hq hr, zero_im] using hb.symm

theorem hillL2UpperBoundaryPrimitive_ground_sheet
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ)
    (hx : x ≤ hillLowestEnergy q hq hr) :
    (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).im = 0 ∧
      0 ≤ (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).re := by
  rcases lt_or_eq_of_le hx with hx | rfl
  · refine ⟨hillL2UpperBoundaryPrimitive_im_eq_zero_below q hq hr x hx, ?_⟩
    apply hillL2UpperBoundaryPrimitive_re_nonneg q hq hr x
    intro he
    have hp := hillL2Radicand_pos_below q hq hr x hx
    simp only [he, zero_re, lt_self_iff_false] at hp
  · simp only [hillL2UpperBoundaryPrimitive_ground q hq hr, zero_im, zero_re, le_refl, and_self]

theorem continuousAt_hillL2GroundSquare
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ)
    (hx : x ≤ hillLowestEnergy q hq hr) :
    ContinuousAt (hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) 0) (x : ℂ) := by
  let F : ℂ → ℂ := fun z => hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q) ^ 2
  let B : ℝ → ℂ := fun y => hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) y ^ 2
  have hconj : conj (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x) =
      hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x := by
    apply Complex.ext <;> simp [(hillL2UpperBoundaryPrimitive_ground_sheet q hq hr x hx).1]
  have hu : Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (B x)) :=
    (tendsto_hillL2UpperBoundaryPrimitive_all q hq hr x).pow 2
  have hl : Tendsto F (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (B x)) := by
    simpa only [hconj, neg_sq] using (tendsto_hillL2ContinuedPrimitive_lower_all q hq hr x).pow 2
  have he : realBoundaryExtension F B = hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) 0 := by
    funext z
    by_cases hz : z.im = 0 <;> simp only [realBoundaryExtension, hillL2RealGapPrimitiveSquare,
      hillL2RealCutPrimitive, F, B, hz, if_true, if_false, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  rw [← he]
  exact continuousAt_realBoundaryExtension_of_limits F B x
    ((continuous_hillL2UpperBoundaryPrimitive q hq hr).pow 2).continuousAt hu hl

theorem analyticAt_hillL2GroundSquare
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ)
    (hx : x ≤ hillLowestEnergy q hq hr) :
    AnalyticAt ℂ (hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) 0) (x : ℂ) := by
  have hs := hillL2UpperBoundaryPrimitive_ground_sheet q hq hr x hx
  have hval : hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) 0 x =
      (((hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).re : ℂ)) ^ 2 := by
    have he : hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x =
        (((hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).re : ℂ)) := by
      apply Complex.ext <;> simp [hs.1]
    simp only [hillL2RealGapPrimitiveSquare, hillL2RealCutPrimitive, ofReal_im, if_true,
      ofReal_re, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    exact congrArg (fun w : ℂ => w ^ 2) he
  apply analyticAt_of_continuousAt_coordinate coshSquareCoordinate
    (hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) 0) x
    (analyticOnNhd_coshSquareCoordinate _ (mem_univ _))
  · rw [hval]
    exact deriv_coshSquareCoordinate_sq_ne_zero _ hs.2
  · exact continuousAt_hillL2GroundSquare q hq hr x hx
  · have he : coshSquareCoordinate ∘ hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) 0 =
        (fun z => hillL2Discriminant (SpectralWeight.one.toCoeff q) z / 2) := by
      funext z
      simpa only [Function.comp_def, pow_zero, one_mul] using hillL2RealGapPrimitiveSquare_cosh q hq hr 0 z
    rw [he]
    exact (analyticOnNhd_hillL2Discriminant _ x (mem_univ _)).div_const

/-- The original cut domain with the lowest ray and all collapsed gap
points filled. Open positive-index gaps and their endpoints remain cuts. -/
def hillL2FilledSquareDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) : Set ℂ :=
  {z | z ∈ hillL2RealCutDomain q hq hr ∨ z.re ≤ hillLowestEnergy q hq hr ∨
    ∃ n : ℕ, 1 ≤ n ∧ hillRealLabels q hq hr (2 * n - 1) = hillRealLabels q hq hr (2 * n) ∧
      z.re = hillRealLabels q hq hr (2 * n - 1)}

theorem isOpen_hillL2FilledSquareDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    IsOpen (hillL2FilledSquareDomain q hq hr) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  by_cases hi : z.im ≠ 0
  · exact Filter.mem_of_superset ((isOpen_ne_fun continuous_im continuous_const).mem_nhds hi)
      (fun _ hw => Or.inl (Or.inl hw))
  rcases hz with hcut | hground | ⟨n, hn, hc, hre⟩
  · exact Filter.mem_of_superset ((isOpen_hillL2RealCutDomain q hq hr).mem_nhds hcut)
      (fun _ hw => Or.inl hw)
  · have hstrict : z.re < hillRealLabels q hq hr 1 := hground.trans_lt (hillRealLabels_band_strict q hq hr 0)
    apply Filter.mem_of_superset ((isOpen_lt continuous_re continuous_const).mem_nhds hstrict)
    intro w hw
    by_cases hw0 : 0 ≤ w.re - hillLowestEnergy q hq hr
    · by_cases he : w.re = hillLowestEnergy q hq hr
      · exact Or.inr (Or.inl he.le)
      · refine Or.inl (Or.inr ⟨0, ?_⟩)
        change hillLowestEnergy q hq hr < w.re ∧ w.re < hillRealLabels q hq hr 1
        exact ⟨lt_of_le_of_ne (by linarith) (Ne.symm he), hw⟩
    · exact Or.inr (Or.inl (by linarith))
  · have hzC : z = (hillRealLabels q hq hr (2 * n - 1) : ℂ) := by
      apply Complex.ext <;> simp [hre, not_ne_iff.mp hi]
    obtain ⟨_, hη, hl, _, hsub⟩ := hillRealGapContour_geometry q hq hr n hn
    have hd0 : hillRealGapHalfLength q hq hr n = 0 := by simp [hillRealGapHalfLength, hc]
    have hcenter : hillRealGapCenter q hq hr n = hillRealLabels q hq hr (2 * n - 1) := by
      simpa only [hd0, sub_zero] using hl
    have hpunc : ball z (2 * hillRealGapCollar q hq hr n) \ {z} ⊆ hillL2RealCutDomain q hq hr := by
      simpa only [hd0, zero_add, hcenter, ← hc, segment_same, ← hzC] using hsub
    apply Filter.mem_of_superset (isOpen_ball.mem_nhds
      (mem_ball_self (by positivity : 0 < 2 * hillRealGapCollar q hq hr n)))
    intro w hw
    by_cases he : w = z
    · exact Or.inr (Or.inr ⟨n, hn, hc, he ▸ hre⟩)
    · exact Or.inl (hpunc ⟨hw, he⟩)

theorem analyticOnNhd_hillL2FilledSquare
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    AnalyticOnNhd ℂ (hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) 0)
      (hillL2FilledSquareDomain q hq hr) := by
  have hzero : hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) 0 =
      (fun z => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ 2) := by
    funext z
    simp only [hillL2RealGapPrimitiveSquare, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  rw [hzero]
  intro z hz
  by_cases hi : z.im ≠ 0
  · exact ((analyticOnNhd_hillL2RealCutPrimitive q hq hr) z (Or.inl hi)).pow 2
  have hzC : z = (z.re : ℂ) := by apply Complex.ext <;> simp [not_ne_iff.mp hi]
  rcases hz with hcut | hground | ⟨n, hn, hc, hre⟩
  · exact ((analyticOnNhd_hillL2RealCutPrimitive q hq hr) z hcut).pow 2
  · rw [hzC, ← hzero]
    exact analyticAt_hillL2GroundSquare q hq hr z.re hground
  · rw [hzC, hre]
    exact (analyticAt_hillL2RealCutPrimitive_collapsed q hq hr n hn hc).pow 2

end NLS.KdV
