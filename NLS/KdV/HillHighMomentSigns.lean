import NLS.KdV.HillRealGapIntegrals
import NLS.KdV.HillCanonicalRealLabels

/-! # Positivity of all sufficiently high real Hill moments

High actual gap labels are positive at the checked elementary cutoff.
The real mean-value relation therefore gives nonnegative moments at every
level in the tail, even though finitely many low moments can be signed.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.KdV

theorem hillRealLabels_high_left_pos
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ)) :
    0 < hillRealLabels q hq hr (2*n-1) := by
  obtain ⟨p, hL, _⟩ := hillRealLabels_high_pair q hq hr n hn hcut
  have hloc := abs_le.mp (p.localization q hq n (by omega) (by linarith [norm_nonneg q])).1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hfree : (n : ℝ)/2 < freeHillValue n := by
    calc
      _ < (n : ℝ)^2 := by nlinarith
      _ ≤ Real.pi^2 * (n : ℝ)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hpi) (sq_nonneg (n : ℝ))]
      _ = _ := by simp only [freeHillValue, Int.cast_natCast]
  rw [hL]
  linarith [hloc.1]

theorem hillRealGapIntegral_high_nonneg
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    0 ≤ hillRealGapIntegral q hq hr n m := by
  have hl := (hillRealLabels_high_left_pos q hq hr n hn hcut).le
  have hI : 0 ≤ hillRealGapIntegral q hq hr n 0 := by
    simpa only [mul_zero] using hillRealGapIntegral_nonneg_even q hq hr n (by omega) 0
  exact (mul_nonneg (pow_nonneg hl m) hI).trans
    (hillRealGapIntegral_bounds_of_nonneg_left q hq hr n (by omega) m hl).1

theorem eventually_hillRealGapIntegral_nonneg
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 ≤ hillRealGapIntegral q hq hr n m := by
  obtain ⟨A, hA⟩ := exists_nat_ge (16*‖q‖)
  filter_upwards [eventually_ge_atTop (max 2 A)] with n hn
  intro m
  apply hillRealGapIntegral_high_nonneg q hq hr n ((le_max_left _ _).trans hn)
  · exact hA.trans (by exact_mod_cast (le_max_right 2 A).trans hn)

end NLS.KdV
