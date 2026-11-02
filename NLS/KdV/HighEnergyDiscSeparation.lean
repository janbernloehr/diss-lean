import NLS.KdV.HighEnergyContourSeparation

/-! # Uniform quadratic separation throughout distinct frequency discs -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

private theorem norm_three_sum_le_discs (a b c : ℂ) :
    ‖a+b+c‖ ≤ ‖a‖+‖b‖+‖c‖ :=
  (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

theorem highEnergyDiscs_separation (n k : ℕ+) (hnk : n ≠ k) (z w : ℂ)
    (hz : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4))
    (hw : w ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)) :
    Real.pi^2/4 * |(k : ℝ)^2-(n : ℝ)^2| ≤ ‖z^2-w^2‖ := by
  have hzn : ‖(Real.pi : ℂ)*(k : ℕ)-z‖ ≤ Real.pi/4 := by
    rw [norm_sub_rev]
    exact mem_closedBall_iff_norm.mp hz
  have hwn : ‖w-(Real.pi : ℂ)*(n : ℕ)‖ ≤ Real.pi/4 := mem_closedBall_iff_norm.mp hw
  have hwrev : ‖(Real.pi : ℂ)*(n : ℕ)-w‖ ≤ Real.pi/4 := by
    rwa [norm_sub_rev]
  have hgap : 1 ≤ |(k : ℝ)-(n : ℝ)| := by
    have hne : (n : ℕ) ≠ (k : ℕ) := fun h => hnk (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · have hn : (n : ℝ)+1 ≤ (k : ℝ) := by exact_mod_cast h
      exact le_trans (by linarith : 1 ≤ (k : ℝ)-(n : ℝ)) (le_abs_self _)
    · have hn : (k : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast h
      exact le_trans (by linarith : 1 ≤ -((k : ℝ)-(n : ℝ))) (neg_le_abs _)
  have hsum : 1 ≤ (k : ℝ)+(n : ℝ) := by
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.property
    linarith
  have hminus : Real.pi/2 * |(k : ℝ)-(n : ℝ)| ≤ ‖z-w‖ := by
    have ht := norm_three_sum_le_discs ((Real.pi : ℂ)*(k : ℕ)-z) (z-w)
      (w-(Real.pi : ℂ)*(n : ℕ))
    have he : (Real.pi : ℂ)*(k : ℕ)-z+(z-w)+(w-(Real.pi : ℂ)*(n : ℕ)) =
        ((Real.pi*((k : ℝ)-(n : ℝ)) : ℝ) : ℂ) := by push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos] at ht
    nlinarith [Real.pi_pos]
  have hplus : Real.pi/2 * ((k : ℝ)+(n : ℝ)) ≤ ‖z+w‖ := by
    have ht := norm_three_sum_le_discs ((Real.pi : ℂ)*(k : ℕ)-z) (z+w)
      ((Real.pi : ℂ)*(n : ℕ)-w)
    have he : (Real.pi : ℂ)*(k : ℕ)-z+(z+w)+((Real.pi : ℂ)*(n : ℕ)-w) =
        ((Real.pi*((k : ℝ)+(n : ℝ)) : ℝ) : ℂ) := by push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)] at ht
    nlinarith [Real.pi_pos]
  have he : z^2-w^2 = (z-w)*(z+w) := by ring
  rw [he,norm_mul]
  have ha : |(k : ℝ)^2-(n : ℝ)^2| = |(k : ℝ)-(n : ℝ)| * ((k : ℝ)+(n : ℝ)) := by
    rw [sq_sub_sq,abs_mul,abs_of_nonneg (by positivity)]
    ring
  rw [ha]
  nlinarith [mul_le_mul hminus hplus (by positivity)
    (norm_nonneg (z-w))]

end NLS.KdV
