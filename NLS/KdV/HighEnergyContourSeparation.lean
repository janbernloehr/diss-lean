import NLS.KdV.ClassicalHighCriticalPoints

/-! # Uniform separation of distinct high Hill critical energies

The fixed frequency circles and the actual critical discs yield the
quadratic energy denominator needed in the infinite period estimates.
-/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

private theorem norm_three_sum_le (a b c : ℂ) :
    ‖a+b+c‖ ≤ ‖a‖+‖b‖+‖c‖ :=
  (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

/-- Half-radius localization also separates the same-mode critical
energy from its contour, with a lower bound growing linearly in n. -/
theorem highEnergyContour_diagonal_separation (n : ℕ+) (z w : ℂ)
    (hz : z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4))
    (hw : w ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/8)) :
    Real.pi^2/8*(n : ℝ) ≤ ‖z^2-w^2‖ := by
  have hzn : ‖(Real.pi : ℂ)*(n : ℕ)-z‖ = Real.pi/4 := by
    rw [norm_sub_rev]
    exact mem_sphere_iff_norm.mp hz
  have hwn : ‖w-(Real.pi : ℂ)*(n : ℕ)‖ ≤ Real.pi/8 := mem_closedBall_iff_norm.mp hw
  have hwrev : ‖(Real.pi : ℂ)*(n : ℕ)-w‖ ≤ Real.pi/8 := by rwa [norm_sub_rev]
  have hminus : Real.pi/8 ≤ ‖z-w‖ := by
    have ht := norm_add_le (z-w) (w-(Real.pi : ℂ)*(n : ℕ))
    have he : z-w+(w-(Real.pi : ℂ)*(n : ℕ)) = z-(Real.pi : ℂ)*(n : ℕ) := by ring
    rw [he,mem_sphere_iff_norm.mp hz] at ht
    linarith
  have hplus : Real.pi*(n : ℝ) ≤ ‖z+w‖ := by
    have ht := norm_three_sum_le ((Real.pi : ℂ)*(n : ℕ)-z) (z+w)
      ((Real.pi : ℂ)*(n : ℕ)-w)
    have he : (Real.pi : ℂ)*(n : ℕ)-z+(z+w)+((Real.pi : ℂ)*(n : ℕ)-w) =
        2*((Real.pi : ℂ)*(n : ℕ)) := by ring
    rw [he,norm_mul,norm_ofNat,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_natCast,hzn] at ht
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.property
    nlinarith [Real.pi_pos]
  have he : z^2-w^2 = (z-w)*(z+w) := by ring
  rw [he,norm_mul]
  nlinarith [mul_le_mul hminus hplus (by positivity) (norm_nonneg (z-w))]

/-- The estimate is uniform in both distinct positive indices and all
points of the selected contour and critical disc. -/
theorem highEnergyContour_separation (n k : ℕ+) (hnk : n ≠ k) (z w : ℂ)
    (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4))
    (hw : w ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)) :
    Real.pi^2/4 * |(k : ℝ)^2-(n : ℝ)^2| ≤ ‖z^2-w^2‖ := by
  have hzn : ‖(Real.pi : ℂ)*(k : ℕ)-z‖ = Real.pi/4 := by
    rw [norm_sub_rev]
    exact mem_sphere_iff_norm.mp hz
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
    have ht := norm_three_sum_le ((Real.pi : ℂ)*(k : ℕ)-z) (z-w)
      (w-(Real.pi : ℂ)*(n : ℕ))
    have he : (Real.pi : ℂ)*(k : ℕ)-z+(z-w)+(w-(Real.pi : ℂ)*(n : ℕ)) =
        ((Real.pi*((k : ℝ)-(n : ℝ)) : ℝ) : ℂ) := by push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos,hzn] at ht
    nlinarith [Real.pi_pos]
  have hplus : Real.pi/2 * ((k : ℝ)+(n : ℝ)) ≤ ‖z+w‖ := by
    have ht := norm_three_sum_le ((Real.pi : ℂ)*(k : ℕ)-z) (z+w)
      ((Real.pi : ℂ)*(n : ℕ)-w)
    have he : (Real.pi : ℂ)*(k : ℕ)-z+(z+w)+((Real.pi : ℂ)*(n : ℕ)-w) =
        ((Real.pi*((k : ℝ)+(n : ℝ)) : ℝ) : ℂ) := by push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity),hzn] at ht
    nlinarith [Real.pi_pos]
  have he : z^2-w^2 = (z-w)*(z+w) := by ring
  rw [he,norm_mul]
  have ha : |(k : ℝ)^2-(n : ℝ)^2| = |(k : ℝ)-(n : ℝ)| * ((k : ℝ)+(n : ℝ)) := by
    rw [sq_sub_sq,abs_mul,abs_of_nonneg (by positivity)]
    ring
  rw [ha]
  nlinarith [mul_le_mul hminus hplus (by positivity)
    (norm_nonneg (z-w))]

/-- In particular, a different critical disc cannot meet the squared contour. -/
theorem highEnergyContour_sub_sq_ne_zero (n k : ℕ+) (hnk : n ≠ k) (z w : ℂ)
    (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4))
    (hw : w ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)) : z^2-w^2 ≠ 0 := by
  have hne : (k : ℝ) ≠ (n : ℝ) := by
    intro he
    apply hnk
    exact_mod_cast he.symm
  have hsum : (0 : ℝ) < (k : ℝ)+(n : ℝ) := by positivity
  have hdiff : (k : ℝ)^2-(n : ℝ)^2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (ne_of_gt hsum) (sub_ne_zero.mpr hne)
  have hp : 0 < Real.pi^2/4 * |(k : ℝ)^2-(n : ℝ)^2| :=
    mul_pos (by positivity) (abs_pos.mpr hdiff)
  exact norm_pos_iff.mp (hp.trans_le (highEnergyContour_separation n k hnk z w hz hw))

/-- Actual critical energies satisfy that separation on one neighborhood
at every continuous complex potential; neither index is fixed first. -/
theorem exists_classicalHill_high_critical_energy_separation (q0 : NLS.LinearVolterra.Curve ℂ) :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), 0 < N ∧ IsOpen V ∧ q0 ∈ V ∧
      ∀ n k : ℕ+, N < (n : ℕ) → N < (k : ℕ) → n ≠ k → ∀ q ∈ V,
        ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
          Real.pi^2/4 * |(k : ℝ)^2-(n : ℝ)^2| ≤
            ‖z^2-classicalHillHighCriticalPoint q n‖ := by
  obtain ⟨N,V,hN,hV,hqV,hhigh⟩ := exists_analytic_classicalHillHighCriticalPoints q0
  refine ⟨N,V,hN,hV,hqV,?_⟩
  intro n k hn _ hnk q hq z hz
  exact highEnergyContour_separation n k hnk z (classicalHillFrequencyCritical q n) hz
    (ball_subset_closedBall ((hhigh n hn).2.2 q hq).1)

end NLS.KdV
