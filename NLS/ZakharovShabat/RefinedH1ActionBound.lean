import NLS.ZakharovShabat.HigherSobolevH1Realization

/-! # A refined H¹ action bound for the constants in Lemma 27.2 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- The nonzero period-one frequencies permit a factor 4/3 in the weight comparison. -/
theorem physical_H1_weight_sq_le_four_thirds (n : ℤ) :
    (1+|((2*n:ℤ):ℝ)*Real.pi|)^2 ≤ (4/3:ℝ)*(1+(2*Real.pi*(n:ℝ))^2) := by
  by_cases hn : n = 0
  · subst n
    norm_num
  have hnat : 1 ≤ |(n:ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hlarge : 6 ≤ 2*Real.pi*|(n:ℝ)| := by nlinarith [Real.pi_gt_three]
  have hnon : 0 ≤ 2*Real.pi*|(n:ℝ)| := by positivity
  simp only [Int.cast_mul, Int.cast_ofNat, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2),
    abs_of_pos Real.pi_pos]
  have he : (2*Real.pi*(n:ℝ))^2 = (2*Real.pi*|(n:ℝ)|)^2 := by
    simp only [mul_pow,sq_abs]
  rw [he]
  nlinarith [mul_nonneg (sub_nonneg.mpr hlarge) hnon]

/-- The total action cannot exceed its bracket-weighted norm. -/
theorem sourceH1_action_mass_le_weighted (a : realTypeSobolevSourceLocus) :
    (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n) ≤
      ∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n := by
  rw [sourceH1_sum_actions_eq_mass]
  have hnon : 0 ≤ ∑' n : ℤ, (sourceSobolevWeightedAction a.val n).re := by
    apply tsum_nonneg
    intro n
    rw [sourceSobolevWeightedAction_re]
    exact mul_nonneg (sq_nonneg _)
      (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
        (sourceH1RealSource a).val (sourceH1RealSource a).property n).1
  linarith [sourceH1_kinetic_actions_add_mass_le a]

/-- The exact physical H¹ norm satisfies the improved factor 8/3. -/
theorem sourceH1_norm_sq_le_eight_thirds_actions (a : realTypeSobolevSourceLocus) :
    ‖sourcePhysicalH1Coordinates a.val‖^2 ≤ (8/3:ℝ)*
      ((∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)^2) := by
  rw [sourceH1_sum_actions_eq_mass]
  have hnorm := sourcePhysicalH1_fst_sq_le_of_weight_bound a.val (4/3)
    physical_H1_weight_sq_le_four_thirds
  have hpair := sourcePhysicalH1_norm_sq_eq_twice_fst a
  have hquartic := periodOneSobolevMass_sq_le_quartic a
  have henergy := sourceH1_energy_le_kinetic_actions a
  have hsum := sourceH1_kinetic_actions_add_mass_le a
  rw [periodOneSobolevHamiltonian, Complex.add_re] at henergy
  rw [← Complex.ofReal_re (‖scalarInclusion a.val.1‖^2), ← periodOneSobolevMass_real_eq a,
    ← Complex.ofReal_re (‖periodOneDerivative a.val.1‖^2), ← periodOneSobolevKinetic_real_eq a] at hnorm
  linarith

end NLS.ZakharovShabat
