import NLS.KdV.SingularHillPhysical
import NLS.KdV.FreeHillRegularity

/-! # A fixed physical isomorphism H1 to H-minus-one

The free operator -d²/dx²+1 is inverted on the entire original period-two
distribution spaces. This provides a fixed Banach-space normalization of
the singular Hill spectral pencil, with the physical pi-squared symbol.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The full free shift is the actual positive Laplacian plus the identity inclusion. -/
def singularHillFreeShift : FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ]
    FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  singularHillLaplacian + singularHillDomainInclusion

theorem singularHillFreeShift_coefficient (f : FourierLebesgueSpace (2:ℝ) 1 2) (k : ℤ) :
    (singularHillFreeShift f).val (mode (-k)) =
      ((1+freeHillValue k:ℝ):ℂ)*f.val (mode (-k)) := by
  change (singularHillLaplacian f).val (mode (-k)) +
    (singularHillDomainInclusion f).val (mode (-k)) = _
  rw [singularHillLaplacian_coefficient, singularHillDomainInclusion_coefficient]
  push_cast
  ring

/-- The inverse free symbol gains exactly two orders in the full original Sobolev scale. -/
theorem singularHillFreeInverse_weight_bound (k : ℤ) :
    Weight.sobolev 1 k * ‖(((1+freeHillValue k:ℝ)⁻¹):ℂ)‖ ≤
      2*Weight.sobolev (-1) k := by
  have hv : 0 ≤ freeHillValue k := by unfold freeHillValue; positivity
  have hA : 0 < 1+freeHillValue k := by linarith
  have hb : 0 < 1+|(k:ℝ)| := by positivity
  have hw := sobolev_two_le_freeHillValue k
  simp only [Weight.sobolev_apply, Real.rpow_two] at hw
  simp only [Weight.sobolev_apply, Real.rpow_one, Real.rpow_neg_one,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ hA).mpr
  calc
    _ ≤ (2*(1+freeHillValue k))/(1+|(k:ℝ)|) :=
      (le_div_iff₀ hb).mpr (by nlinarith)
    _ = _ := by ring

/-- The inverse of the free shift on the full original H-minus-one space. -/
def singularHillFreeInverse : FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ]
    FourierLebesgueSpace (2:ℝ) 1 2 :=
  (sobolevCoefficients 1 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WeightedCoeff.weightedMultiplierCLM _ _
      (fun k => (((1+freeHillValue k:ℝ)⁻¹):ℂ)) 2 (by norm_num)
        singularHillFreeInverse_weight_bound).comp
      (sobolevCoefficients (-1) 2).toContinuousLinearEquiv.toContinuousLinearMap)

theorem singularHillFreeInverse_coefficient (g : FourierLebesgueSpace (2:ℝ) (-1) 2) (k : ℤ) :
    (singularHillFreeInverse g).val (mode (-k)) =
      (((1+freeHillValue k:ℝ)⁻¹):ℂ)*g.val (mode (-k)) := by
  change ((sobolevCoefficients 1 2) ((sobolevCoefficients 1 2).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The full free shift has a right inverse on every original H-minus-one datum. -/
theorem singularHillFreeShift_inverse (g : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    singularHillFreeShift (singularHillFreeInverse g) = g := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [singularHillFreeShift_coefficient, singularHillFreeInverse_coefficient,
    ← mul_assoc, mul_inv_cancel₀, one_mul]
  apply Complex.ofReal_ne_zero.mpr
  have hv : 0 ≤ freeHillValue k := by unfold freeHillValue; positivity
  linarith

/-- The free inverse also recovers every vector of the entire original H1 domain. -/
theorem singularHillFreeInverse_shift (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillFreeInverse (singularHillFreeShift f) = f := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [singularHillFreeInverse_coefficient, singularHillFreeShift_coefficient,
    ← mul_assoc, inv_mul_cancel₀, one_mul]
  apply Complex.ofReal_ne_zero.mpr
  have hv : 0 ≤ freeHillValue k := by unfold freeHillValue; positivity
  linarith

/-- A fixed physical Banach-space isomorphism, without a spectral parameter or potential. -/
def singularHillFreeIsomorphism : FourierLebesgueSpace (2:ℝ) 1 2 ≃L[ℂ]
    FourierLebesgueSpace (2:ℝ) (-1) 2 where
  toLinearEquiv :=
    { toLinearMap := singularHillFreeShift.toLinearMap
      invFun := singularHillFreeInverse
      left_inv := singularHillFreeInverse_shift
      right_inv := singularHillFreeShift_inverse }
  continuous_toFun := singularHillFreeShift.continuous
  continuous_invFun := singularHillFreeInverse.continuous

end NLS.KdV
