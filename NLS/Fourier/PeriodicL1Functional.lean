import NLS.Fourier.IntervalCoefficientScaling
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! # Normalized action of interval L1 data on continuous periodic tests

No square-integrability or boundedness assumption is imposed on the input.
The action has exactly the source factor 1/L and extends continuously from
continuous periodic tests to the distributional construction below.
-/
noncomputable section
open MeasureTheory Set
namespace NLS.Fourier
variable (L : ℝ) [Fact (0 < L)]

/-- The normalized L1 norm on one fundamental interval. -/
def periodicL1Size (f : ℝ → ℂ) : ℝ := L⁻¹ * ∫ x in (0 : ℝ)..L, ‖f x‖

theorem periodicL1Size_nonneg (f : ℝ → ℂ) : 0 ≤ periodicL1Size L f :=
  mul_nonneg (inv_nonneg.mpr (le_of_lt (Fact.out : 0 < L)))
    (intervalIntegral.integral_nonneg_of_forall (le_of_lt (Fact.out : 0 < L)) (fun _ => norm_nonneg _))

omit [Fact (0 < L)] in
theorem intervalIntegrable_mul_circleTest (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L)
    (g : C(AddCircle L, ℂ)) : IntervalIntegrable (fun x => f x*g (x : AddCircle L)) volume 0 L :=
  hf.mul_continuousOn ((g.continuous.comp (by fun_prop)).continuousOn)

/-- A norm bound in the original physical normalization. -/
theorem norm_periodicL1Action_le (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L)
    (g : C(AddCircle L, ℂ)) :
    ‖(L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, f x*g (x : AddCircle L)‖ ≤ periodicL1Size L f*‖g‖ := by
  have hL : 0 < L := Fact.out
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  calc
    _ ≤ L⁻¹ * ∫ x in (0 : ℝ)..L, ‖f x*g (x : AddCircle L)‖ :=
      mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hL.le) (by positivity)
    _ ≤ L⁻¹ * ∫ x in (0 : ℝ)..L, ‖f x‖*‖g‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply intervalIntegral.integral_mono_on hL.le (intervalIntegrable_mul_circleTest L f hf g).norm (hf.norm.mul_const _)
      intro x _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (norm_nonneg _)
    _ = _ := by rw [intervalIntegral.integral_mul_const]; exact (mul_assoc _ _ _).symm

/-- The normalized bounded functional on all continuous periodic tests. -/
def periodicL1Functional (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) :
    C(AddCircle L, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun g => (L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, f x*g (x : AddCircle L)
      map_add' := fun g h => by
        simp only [ContinuousMap.add_apply,mul_add]
        rw [intervalIntegral.integral_add (intervalIntegrable_mul_circleTest L f hf g)
          (intervalIntegrable_mul_circleTest L f hf h),mul_add]
      map_smul' := fun c g => by
        simp only [ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply]
        simp_rw [show ∀ x : ℝ, f x*(c*g (x : AddCircle L)) = c*(f x*g (x : AddCircle L)) by intro x; ring]
        rw [intervalIntegral.integral_const_mul]
        ring }
    (periodicL1Size L f) (norm_periodicL1Action_le L f hf)

@[simp] theorem periodicL1Functional_apply (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L)
    (g : C(AddCircle L, ℂ)) : periodicL1Functional L f hf g =
      (L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, f x*g (x : AddCircle L) := rfl

theorem norm_periodicL1Functional_le (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) :
    ‖periodicL1Functional L f hf‖ ≤ periodicL1Size L f :=
  ContinuousLinearMap.opNorm_le_bound _ (periodicL1Size_nonneg L f) (norm_periodicL1Action_le L f hf)

/-- On a negative wave, the functional is exactly the source's normalized coefficient. -/
theorem periodicL1Functional_fourier (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) (n : ℤ) :
    periodicL1Functional L f hf (fourier n) = intervalFourierCoefficient L f (-n) := by
  rw [periodicL1Functional_apply,intervalFourierCoefficient_eq_fourierCoeffOn (Fact.out : 0 < L),fourierCoeffOn_eq_integral]
  simp only [neg_neg,sub_zero,smul_eq_mul,Complex.real_smul]
  push_cast
  simp only [one_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only [fourier_coe_apply, sub_zero]
  ring

/-- Every actual Fourier coefficient is bounded by the normalized L1 norm. -/
theorem norm_intervalFourierCoefficient_le_L1 (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) (n : ℤ) :
    ‖intervalFourierCoefficient L f n‖ ≤ periodicL1Size L f := by
  have h := (periodicL1Functional L f hf).le_of_opNorm_le (norm_periodicL1Functional_le L f hf) (fourier (-n))
  simpa only [periodicL1Functional_fourier,neg_neg,fourier_norm,mul_one] using h

end NLS.Fourier
