import NLS.KdV.HillOuterTraceGeometry

/-! # The actual outer Hill circles escape to infinity -/

noncomputable section
open Set Metric Complex Filter
namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
variable (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
variable (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillRealOuterUpper_high_lower (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8 * ‖q‖ ≤ (n : ℝ)) :
    (n : ℝ) - 4 * ‖q‖ ≤ hillRealOuterUpper q hq hr n := by
  obtain ⟨p, _, hu⟩ := hillRealLabels_high_pair q hq hr n hn hcut
  have hp := (abs_le.mp (p.localization q hq n (by omega) hcut).2).1
  have hb := (hillRealOuterUpper_mem_band q hq hr n).1
  rw [hu] at hb
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hπ : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hfree : (n : ℝ) ≤ freeHillValue n := by
    simp only [freeHillValue, Int.cast_natCast]
    nlinarith [sq_nonneg (n : ℝ)]
  linarith

theorem tendsto_hillRealOuterUpper :
    Tendsto (hillRealOuterUpper q hq hr) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  obtain ⟨K, hK⟩ := exists_nat_ge (max (8 * ‖q‖) (b + 4 * ‖q‖))
  filter_upwards [eventually_ge_atTop (max 2 K)] with n hn
  have hKn : (K : ℝ) ≤ n := by exact_mod_cast (show K ≤ n by omega)
  have hc : 8 * ‖q‖ ≤ (n : ℝ) := (le_max_left _ _).trans (hK.trans hKn)
  have hb : b + 4 * ‖q‖ ≤ (n : ℝ) := (le_max_right _ _).trans (hK.trans hKn)
  exact (by linarith : b ≤ (n : ℝ) - 4 * ‖q‖).trans
    (hillRealOuterUpper_high_lower q hq hr n (by omega) hc)

theorem tendsto_hillRealOuterRadius :
    Tendsto (hillRealOuterRadius q hq hr) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_hillRealOuterUpper q hq hr))
    (b + hillRealOuterCenter q hq hr)] with N hN
  dsimp [hillRealOuterRadius]
  linarith

/-- Every point of the outer circle eventually has arbitrarily large modulus. -/
theorem hillRealOuter_sphere_eventually_norm_ge (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ,
      z ∈ sphere (hillRealOuterCenter q hq hr : ℂ) (hillRealOuterRadius q hq hr N) →
        A ≤ ‖z‖ := by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_hillRealOuterRadius q hq hr))
    (A + ‖(hillRealOuterCenter q hq hr : ℂ)‖)] with N hN
  intro z hz
  have hs : ‖z - (hillRealOuterCenter q hq hr : ℂ)‖ = hillRealOuterRadius q hq hr N :=
    mem_sphere_iff_norm.mp hz
  have ht := norm_sub_le z (hillRealOuterCenter q hq hr : ℂ)
  linarith

end NLS.KdV
