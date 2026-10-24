import NLS.ZakharovShabat.L2WholeLineUnitModeNotL2

/-! # No nonzero physical Floquet mode is globally square integrable -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Matrix
namespace NLS.ZakharovShabat

/-- Translation invariance of the full mass would force the multiplier
of an L2 Floquet mode onto the unit circle, where periodic mass rules it out. -/
theorem not_memLp_l2WholeLineSolution_of_floquet (u : IntervalPairL2) (z μ : ℂ)
    (hμ : μ ≠ 0) (v : Fin 2 → ℂ) (hv0 : v ≠ 0)
    (hv : l2Monodromy u z *ᵥ v = μ • v) :
    ¬ MemLp (l2WholeLineSolution u z v) 2 volume := by
  intro hF
  have hi : Integrable (wholeLineSolutionMass u z v) :=
    (memLp_wholeLineVector_of_pair _ hF).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hpos : 0 < ∫ t : ℝ, wholeLineSolutionMass u z v t := by
    apply lt_of_lt_of_le (wholeLineSolution_unit_mass_pos u z v hv0)
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact setIntegral_le_integral hi (Filter.Eventually.of_forall (fun t => sq_nonneg _))
  have hshift (t : ℝ) : wholeLineSolutionMass u z v (t+1) =
      ‖μ‖^2 * wholeLineSolutionMass u z v t := by
    have ht := l2WholeLineSolution_add_int_of_eigenvector u z μ hμ v hv t 1
    simp only [Int.cast_one,zpow_one] at ht
    unfold wholeLineSolutionMass
    rw [ht]
    change ‖μ • (WithLp.toLp 2 (l2WholeLineSolution u z v t) : WholeLineVector)‖^2 = _
    rw [norm_smul,mul_pow]
  have he : (∫ t : ℝ, wholeLineSolutionMass u z v t) =
      ‖μ‖^2 * ∫ t : ℝ, wholeLineSolutionMass u z v t := by
    rw [← integral_const_mul]
    simp_rw [← hshift]
    exact (integral_add_right_eq_self _ (1 : ℝ)).symm
  have hunit : ‖μ‖ = 1 := by
    have hsq : ‖μ‖^2 = 1 := mul_right_cancel₀ hpos.ne' (by simpa using he.symm)
    nlinarith [norm_nonneg μ]
  exact not_memLp_l2WholeLineSolution_of_unit_floquet u z μ hunit v hv0 hv hF

end NLS.ZakharovShabat
