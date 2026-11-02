import NLS.KdV.HillL2HighGapMoments

/-! # Uniform comparison of high Hill hierarchy levels

The exact gap mean-value relation and actual endpoint localization prove
the high-index part of Proposition 5. The quantitative source cutoff is
eight in the checked spectral construction. No low-gap comparison or
Hamiltonian trace identity is assumed.
-/

noncomputable section
open Set Complex
namespace NLS.KdV

theorem hillRealGap_point_localization
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8 * ‖q‖ ≤ (n : ℝ)) (x : ℝ)
    (hx : x ∈ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :
    |x - freeHillValue n| ≤ 4 * ‖q‖ := by
  obtain ⟨p, hl, hu⟩ := hillRealLabels_high_pair q hq hr n hn hcut
  rw [hl, hu] at hx
  have hp := p.localization q hq n (by omega) hcut
  rw [abs_le]
  constructor <;> linarith [(abs_le.mp hp.1).1, (abs_le.mp hp.2).2, hx.1, hx.2]

theorem hillRealGap_point_high_bounds
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8 * ‖q‖ ≤ (n : ℝ)) (x : ℝ)
    (hx : x ∈ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :
    freeHillValue n / 2 ≤ x ∧ x ≤ 2 * freeHillValue n := by
  have hloc := hillRealGap_point_localization q hq hr n hn hcut x hx
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hfree : (n : ℝ) ≤ freeHillValue n := by
    have hpi : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    simp only [freeHillValue, Int.cast_natCast]
    nlinarith [mul_lt_mul_of_pos_right hpi (sq_pos_of_pos (by linarith : (0 : ℝ) < n))]
  constructor <;> linarith [(abs_le.mp hloc).1, (abs_le.mp hloc).2]

/-- The high-index part of source Proposition 5, retaining the checked cutoff eight. -/
theorem hillRealGapIntegral_high_comparison
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8 * ‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    (1 / 2 : ℝ) ^ m * (freeHillValue n) ^ m * hillRealGapIntegral q hq hr n 0 ≤
        hillRealGapIntegral q hq hr n m ∧
      hillRealGapIntegral q hq hr n m ≤
        2 ^ m * (freeHillValue n) ^ m * hillRealGapIntegral q hq hr n 0 := by
  obtain ⟨c, hc, he⟩ := hillRealGapIntegral_mean_value q hq hr n (by omega) m
  have hb := hillRealGap_point_high_bounds q hq hr n hn hcut c hc
  have hI : 0 ≤ hillRealGapIntegral q hq hr n 0 := by
    simpa only [mul_zero] using hillRealGapIntegral_nonneg_even q hq hr n (by omega) 0
  have hf : 0 ≤ freeHillValue n := by unfold freeHillValue; positivity
  rw [he]
  constructor
  · have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hb.1 m) hI
    convert! hp using 1
    simp only [div_pow, one_pow]
    ring
  · simpa only [mul_pow] using
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ((by positivity : 0 ≤ freeHillValue n / 2).trans hb.1) hb.2 m) hI

theorem hillL2HighContourMoment_high_comparison
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8 * ‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    (1 / 2 : ℝ) ^ m * (freeHillValue n) ^ m *
        (hillL2HighContourMoment n 0 (SpectralWeight.one.toCoeff q)).re ≤
        (hillL2HighContourMoment n m (SpectralWeight.one.toCoeff q)).re ∧
      (hillL2HighContourMoment n m (SpectralWeight.one.toCoeff q)).re ≤
        2 ^ m * (freeHillValue n) ^ m *
          (hillL2HighContourMoment n 0 (SpectralWeight.one.toCoeff q)).re := by
  simp only [hillL2HighContourMoment_eq_gapIntegral q hq hr n hn hcut, ofReal_re]
  exact hillRealGapIntegral_high_comparison q hq hr n hn hcut m

end NLS.KdV
