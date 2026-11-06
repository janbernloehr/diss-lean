import NLS.KdV.HillHierarchyMomentContinuity
import Mathlib.Tactic

/-! # Global high and central actual spectral bounds for every hierarchy moment. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV
theorem hillRealLabels_high_left_ge
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    (Real.pi^2-1)*(n : ℝ)^2 ≤ hillRealLabels q hq hr (2*n-1) := by
  obtain ⟨p,hL,_⟩ := hillRealLabels_high_pair q hq hr n hn hcut
  have hloc := abs_le.mp (p.localization q hq n (by omega) hcut).1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [hL]
  dsimp only [freeHillValue] at hloc
  simp only [Int.cast_natCast] at hloc
  nlinarith [hloc.1]

theorem hillRealGapIntegral_high_power_lower
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    (Real.pi^2-1)^m*(n : ℝ)^(2*m)*hillRealGapIntegral q hq hr n 0 ≤
      hillRealGapIntegral q hq hr n m := by
  have hL := hillRealLabels_high_left_ge q hq hr n hn hcut
  have hbase : 0 ≤ (Real.pi^2-1)*(n : ℝ)^2 :=
    mul_nonneg (by nlinarith [Real.pi_gt_three]) (sq_nonneg (n : ℝ))
  have hI : 0 ≤ hillRealGapIntegral q hq hr n 0 := by
    simpa only [mul_zero] using hillRealGapIntegral_nonneg_even q hq hr n (by omega) 0
  have hp := pow_le_pow_left₀ hbase hL m
  rw [mul_pow, ← pow_mul] at hp
  exact (mul_le_mul_of_nonneg_right hp hI).trans
    (hillRealGapIntegral_bounds_of_nonneg_left q hq hr n (by omega) m (hbase.trans hL)).1

theorem hillRealLabels_central_abs_le
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) (j : ℕ) (hj : j ≤ 2*N) :
    |hillRealLabels q hq hr j| ≤ (Real.pi^2+1)*(N : ℝ)^2 := by
  have hlo := (hillLowestEnergy_mem_centralInterval q hq hr N hN hcut).1
  have hmono := monotone_hillRealLabels q hq hr
  have hlow := hmono (Nat.zero_le j)
  have hhigh := (hmono hj).trans (hillRealLabels_high_right_le q hq hr N hN hcut)
  change -(N : ℝ)^2 < hillRealLabels q hq hr 0 at hlo
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg Real.pi, sq_nonneg (N : ℝ)],hhigh⟩

theorem hillRealGapIntegral_central_abs_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ))
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (m : ℕ) :
    |hillRealGapIntegral q hq hr n m| ≤
      ((Real.pi^2+1)*(N : ℝ)^2)^m*hillRealGapIntegral q hq hr n 0 := by
  obtain ⟨c,hc,he⟩ := hillRealGapIntegral_mean_value q hq hr n hn m
  have hL := (abs_le.mp (hillRealLabels_central_abs_le q hq hr N hN hcut (2*n-1) (by omega))).1
  have hR := (abs_le.mp (hillRealLabels_central_abs_le q hq hr N hN hcut (2*n) (by omega))).2
  have habs : |c| ≤ (Real.pi^2+1)*(N : ℝ)^2 := abs_le.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have hI : 0 ≤ hillRealGapIntegral q hq hr n 0 := by
    simpa only [mul_zero] using hillRealGapIntegral_nonneg_even q hq hr n hn 0
  rw [he, abs_mul, abs_pow, abs_of_nonneg hI]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg c) habs m) hI


end NLS.KdV
