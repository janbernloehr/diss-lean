import NLS.ZakharovShabat.ResonantDeterminantAnalytic

/-!
# Determinant localization and boundary comparison

The numerical coefficient bounds in Lemma 6.9 force every zero into a
smaller closed disc. On the circle of radius `π/4`, the determinant differs
strictly less from the centered square than the modulus of that square.
These estimates do not assume that zeros are distinct or real.
-/

noncomputable section
namespace NLS.ZakharovShabat

/-- The open disc used for the refined roots in Lemma 6.9. -/
def refinedResonantDisk (n : ℤ) : Set ℂ := Metric.ball ((Real.pi : ℂ)*n) (Real.pi/4)

/-- Every closed disc of radius at most half the lattice spacing lies in the full strip. -/
theorem closedBall_subset_resonantStrip (n : ℤ) {r : ℝ} (hr : r ≤ Real.pi/2) :
    Metric.closedBall ((Real.pi : ℂ)*n) r ⊆ resonantStrip n := by
  intro z hz
  have hd : ‖z - (Real.pi : ℂ)*n‖ ≤ r := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz
  have hre := Complex.abs_re_le_norm (z - (Real.pi : ℂ)*n)
  have he : (z - (Real.pi : ℂ)*n).re = z.re - Real.pi*n := by simp
  rw [he] at hre
  exact hre.trans (hd.trans hr)

/-- The refined disc lies strictly within the source strip. -/
theorem refinedResonantDisk_subset_strip (n : ℤ) : refinedResonantDisk n ⊆ resonantStrip n :=
  Metric.ball_subset_closedBall.trans (closedBall_subset_resonantStrip n (by linarith [Real.pi_pos]))

/-- Algebraic error estimate for a common-diagonal two-by-two determinant. -/
theorem norm_resonant_quadratic_error_le (q a b c : ℂ) :
    ‖((q-a)^2-b*c)-q^2‖ ≤ 2*‖q‖*‖a‖ + ‖a‖^2 + ‖b‖*‖c‖ := by
  have he : ((q-a)^2-b*c)-q^2 = (-(2*q*a)+a^2)-b*c := by ring
  rw [he]
  calc
    _ ≤ (‖-(2*q*a)‖ + ‖a^2‖) + ‖b*c‖ := (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by simp [norm_pow]

/-- Under the source coefficient bounds every scalar zero has distance at most `3π/32` from the center. -/
theorem norm_resonant_quadratic_root_le (q a b c : ℂ)
    (ha : ‖a‖ ≤ Real.pi/32) (hb : ‖b‖ ≤ Real.pi/16) (hc : ‖c‖ ≤ Real.pi/16)
    (hz : (q-a)^2-b*c = 0) : ‖q‖ ≤ 3*Real.pi/32 := by
  have he : ‖q-a‖^2 = ‖b‖*‖c‖ := by
    have h := congrArg norm (sub_eq_zero.mp hz)
    simpa only [norm_pow, norm_mul] using h
  have hp : ‖b‖*‖c‖ ≤ (Real.pi/16)^2 := by
    calc
      _ ≤ (Real.pi/16)*(Real.pi/16) := mul_le_mul hb hc (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hqa : ‖q-a‖ ≤ Real.pi/16 := by nlinarith [norm_nonneg (q-a), Real.pi_pos]
  have ht := norm_le_norm_sub_add q a
  linarith

/-- On the radius-`π/4` circle the centered square strictly dominates the determinant perturbation. -/
theorem norm_resonant_quadratic_error_lt (q a b c : ℂ) (hq : ‖q‖ = Real.pi/4)
    (ha : ‖a‖ ≤ Real.pi/32) (hb : ‖b‖ ≤ Real.pi/16) (hc : ‖c‖ ≤ Real.pi/16) :
    ‖((q-a)^2-b*c)-q^2‖ < ‖q^2‖ := by
  apply (norm_resonant_quadratic_error_le q a b c).trans_lt
  calc
    _ ≤ 2*(Real.pi/4)*(Real.pi/32) + (Real.pi/32)^2 + (Real.pi/16)*(Real.pi/16) := by
      rw [hq]
      gcongr
    _ < ‖q^2‖ := by rw [norm_pow, hq]; nlinarith [sq_pos_of_pos Real.pi_pos]

end NLS.ZakharovShabat
