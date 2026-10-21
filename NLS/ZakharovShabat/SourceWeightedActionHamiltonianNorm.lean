import NLS.ZakharovShabat.SourceWeightedActionHamiltonian

/-! # Comparison with the standard order-two action norm -/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem sourceEnergyAction_standard_weight_le (n : ℤ) :
    Weight.sobolev 2 n ≤ sourceEnergyActionWeight.toWeight n := by
  simp only [Weight.sobolev_apply, sourceEnergyActionWeight,
    SpectralWeight.scaledSobolev_apply, Real.rpow_two]
  have h : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hn := mul_le_mul_of_nonneg_right h (abs_nonneg (n : ℝ))
  nlinarith [abs_nonneg (n : ℝ), mul_nonneg Real.pi_pos.le (abs_nonneg (n : ℝ))]

private theorem sourceEnergyAction_weight_le_standard (n : ℤ) :
    sourceEnergyActionWeight.toWeight n * ‖(1 : ℂ)‖ ≤
      (2 * Real.pi)^2 * Weight.sobolev 2 n := by
  simp only [norm_one, mul_one, Weight.sobolev_apply, sourceEnergyActionWeight,
    SpectralWeight.scaledSobolev_apply, Real.rpow_two]
  have h : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hn := mul_nonneg (abs_nonneg (n : ℝ)) (sub_nonneg.mpr h)
  nlinarith [sq_nonneg (2 * Real.pi - 1),
    mul_nonneg (sq_nonneg (2 * Real.pi - 1)) (abs_nonneg (n : ℝ))]

/-- Coefficient-preserving inclusion into the standard order-two ell1 space. -/
def sourceEnergyActionsToStandard : SourceEnergyActions →L[ℂ] WeightedCoeff (Weight.sobolev 2) 1 :=
  WeightedCoeff.inclusionCLM _ _ sourceEnergyAction_standard_weight_le

/-- The standard and physical weighted action norms have the same topology. -/
def sourceStandardToEnergyActions : WeightedCoeff (Weight.sobolev 2) 1 →L[ℂ] SourceEnergyActions :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun _ => 1) ((2 * Real.pi)^2)
    (sq_nonneg _) sourceEnergyAction_weight_le_standard

@[simp] theorem sourceEnergyActionsToStandard_apply (a : SourceEnergyActions) (n : ℤ) :
    (sourceEnergyActionsToStandard a).val n = a.val n :=
  WeightedCoeff.inclusionCLM_apply _ _ _ a n

@[simp] theorem sourceStandardToEnergyActions_apply
    (a : WeightedCoeff (Weight.sobolev 2) 1) (n : ℤ) :
    (sourceStandardToEnergyActions a).val n = a.val n := by
  change (1 : ℂ) * a.val n = a.val n
  exact one_mul _

/-- The exact bounds compare the two norms without changing coefficients. -/
theorem sourceEnergyActions_norm_comparison (a : SourceEnergyActions) :
    ‖sourceEnergyActionsToStandard a‖ ≤ ‖a‖ ∧
      ‖a‖ ≤ (2 * Real.pi)^2 * ‖sourceEnergyActionsToStandard a‖ := by
  have he : sourceStandardToEnergyActions (sourceEnergyActionsToStandard a) = a := by
    apply Subtype.ext
    funext n
    simp only [sourceStandardToEnergyActions_apply, sourceEnergyActionsToStandard_apply]
  refine ⟨WeightedCoeff.norm_inclusionCLM_le _ _ _ a, ?_⟩
  have h := WeightedCoeff.norm_weightedMultiplier_le _ _ (fun _ => (1 : ℂ))
    ((2 * Real.pi)^2) (sq_nonneg _) sourceEnergyAction_weight_le_standard
    (sourceEnergyActionsToStandard a)
  change ‖sourceStandardToEnergyActions (sourceEnergyActionsToStandard a)‖ ≤ _ at h
  rwa [he] at h

/-- The two action spaces are continuously linearly equivalent through
the identity on every raw action coefficient. -/
def sourceEnergyActionsStandardEquiv : SourceEnergyActions ≃L[ℂ] WeightedCoeff (Weight.sobolev 2) 1 where
  toLinearEquiv :=
    { toLinearMap := sourceEnergyActionsToStandard.toLinearMap
      invFun := sourceStandardToEnergyActions
      left_inv a := by
        change sourceStandardToEnergyActions (sourceEnergyActionsToStandard a) = a
        apply Subtype.ext
        funext n
        simp only [sourceStandardToEnergyActions_apply, sourceEnergyActionsToStandard_apply]
      right_inv a := by
        change sourceEnergyActionsToStandard (sourceStandardToEnergyActions a) = a
        apply Subtype.ext
        funext n
        simp only [sourceEnergyActionsToStandard_apply, sourceStandardToEnergyActions_apply] }
  continuous_toFun := sourceEnergyActionsToStandard.continuous
  continuous_invFun := sourceStandardToEnergyActions.continuous

end NLS.ZakharovShabat
