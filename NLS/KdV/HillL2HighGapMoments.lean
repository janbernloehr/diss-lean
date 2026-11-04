import NLS.KdV.HillL2GapContourIntegral
import NLS.KdV.HillL2CollapsedGapMoments

/-! # Actual high Hill moments as positive real-gap integrals

This proves the real-gap action formula and the exact weighted mean-value
relation for the actual source moments at all integer hierarchy levels.
Both open and collapsed intrinsic gaps are included at the cutoff eight.
-/

noncomputable section
open Set Metric Complex
namespace NLS.KdV

/-- Source formula (7), with the physical orientation and factor `2/π`,
for every intrinsic high gap of the actual rough Hill discriminant. -/
theorem hillL2HighContourMoment_eq_gapIntegral
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8 * ‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    hillL2HighContourMoment n m (SpectralWeight.one.toCoeff q) =
      (hillRealGapIntegral q hq hr n m : ℂ) := by
  by_cases hc : hillRealLabels q hq hr (2 * n - 1) = hillRealLabels q hq hr (2 * n)
  · exact hillL2HighContourMoment_eq_gapIntegral_of_closed q hq hr n hn hcut hc m
  obtain ⟨p, hl, hu⟩ := hillRealLabels_high_pair q hq hr n hn hcut
  have hopen : p.left ≠ p.right := by intro he; exact hc (hl.trans (he.trans hu.symm))
  obtain ⟨R, F, h⟩ := p.exists_normalized_source_cut_primitive q hq n (by omega) hcut
  have hi := h.circleIntegral_shifted_eq_gap q hq hr n hn hcut p hopen R F m
  rw [h.circleIntegral_shifted_eq q hq n (by omega) hcut p R F m] at hi
  rw [h.moment_eq m, hi]
  unfold hillRealGapIntegral
  rw [hl, hu]
  simp_rw [← ofReal_pow, ← ofReal_mul]
  rw [intervalIntegral.integral_ofReal]
  push_cast
  ring

theorem hillL2HighContourMoment_nonneg_even
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8 * ‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    0 ≤ (hillL2HighContourMoment n (2 * m) (SpectralWeight.one.toCoeff q)).re := by
  rw [hillL2HighContourMoment_eq_gapIntegral q hq hr n hn hcut, ofReal_re]
  exact hillRealGapIntegral_nonneg_even q hq hr n (by omega) m

theorem hillL2HighContourMoment_pos_iff
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8 * ‖q‖ ≤ (n : ℝ)) :
    0 < (hillL2HighContourMoment n 0 (SpectralWeight.one.toCoeff q)).re ↔
      hillRealLabels q hq hr (2 * n - 1) < hillRealLabels q hq hr (2 * n) := by
  rw [hillL2HighContourMoment_eq_gapIntegral q hq hr n hn hcut, ofReal_re]
  exact hillRealGapIntegral_pos_iff q hq hr n (by omega)

/-- Source formula (8), now for the actual contour moments. -/
theorem hillL2HighContourMoment_mean_value
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8 * ‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    ∃ c ∈ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n)),
      hillL2HighContourMoment n m (SpectralWeight.one.toCoeff q) =
        (c : ℂ) ^ m * hillL2HighContourMoment n 0 (SpectralWeight.one.toCoeff q) := by
  obtain ⟨c, hc, he⟩ := hillRealGapIntegral_mean_value q hq hr n (by omega) m
  refine ⟨c, hc, ?_⟩
  rw [hillL2HighContourMoment_eq_gapIntegral q hq hr n hn hcut,
    hillL2HighContourMoment_eq_gapIntegral q hq hr n hn hcut, he]
  push_cast
  rfl

end NLS.KdV
