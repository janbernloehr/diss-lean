import NLS.ZakharovShabat.ClassicalMassCorrection
import NLS.ComplexAnalysis.ExponentialVolterraApproximation

/-! # The physical mass coefficient of the classical discriminant

For every continuous complex potential, the first correction to the upper
normalized trace is its bilinear physical mass divided by twice the height.
No differentiability, finite-gap, or real-type assumption is required.
-/
noncomputable section
open Set Complex MeasureTheory intervalIntegral Filter Topology
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The bilinear mass of the original continuous potential on one period. -/
def classicalPhysicalMass (φ : Curve (ℂ × ℂ)) : ℂ :=
  ∫ s in (0 : ℝ)..1, (NLS.LinearVolterra.extend φ s).1 * (NLS.LinearVolterra.extend φ s).2

private theorem twice_I_vertical (y : ℝ) : 2*I*((y : ℂ)*I) = -(2*y : ℂ) := by
  calc
    _ = (2*y : ℂ)*(I*I) := by ring
    _ = _ := by rw [I_mul_I]; ring

private theorem I_vertical (y : ℝ) : I*((y : ℂ)*I) = -(y : ℂ) := by
  calc
    _ = (y : ℂ)*(I*I) := by ring
    _ = _ := by rw [I_mul_I]; ring

/-- The explicit quadratic correction recovers the bilinear physical mass. -/
theorem tendsto_classicalUpperMassCorrection_scaled (φ : Curve (ℂ × ℂ)) :
    Tendsto (fun y : ℝ => (2*y : ℂ) * classicalUpperMassCorrection φ ((y : ℂ)*I) 1)
      atTop (𝓝 (classicalPhysicalMass φ)) := by
  have h := (tendsto_integral_mul_scaled_exponentialVolterra
    (continuous_extend φ).fst (continuous_extend φ).snd ‖φ‖ (norm_nonneg _)
    (fun s _ => (norm_snd_le _).trans (φ.norm_coe_le_norm _))).comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  change Tendsto _ _ (𝓝 (classicalPhysicalMass φ)) at h
  convert h using 1
  ext y
  simp only [Function.comp_apply, id_eq, classicalUpperMassCorrection, twice_I_vertical,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  ring

/-- After multiplication by the height, the remainder beyond the quadratic
correction still tends to zero. -/
theorem tendsto_classicalDiscriminant_massCorrection_remainder (φ : Curve (ℂ × ℂ)) :
    Tendsto (fun y : ℝ => (2*y : ℂ) *
      (exp (-(y : ℂ)) * classicalDiscriminant φ ((y : ℂ)*I) -
        (1 + exp (-(2*y : ℂ))) - classicalUpperMassCorrection φ ((y : ℂ)*I) 1))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    ((tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).const_div_atTop
      (2*‖φ‖^4 + 2*‖φ‖^2))
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (‖φ‖^2)] with y hy hlarge
  have hb := norm_classicalDiscriminant_upper_sub_massCorrection_le φ ((y : ℂ)*I)
    (by simpa using hy) (by simpa using hlarge)
  rw [I_vertical, twice_I_vertical] at hb
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
    Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at hb
  have hn : ‖(2*y : ℂ)‖ = 2*y := by
    rw [show (2*y : ℂ) = ((2*y : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2*y)]
  rw [norm_mul, hn]
  calc
    _ ≤ (2*y) * ((2*‖φ‖^4 + 2*‖φ‖^2)/(2*y)^2) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (2*‖φ‖^4 + 2*‖φ‖^2)/(2*y) := by field_simp

/-- The first high-energy coefficient of the actual discriminant is the
physical mass, with the exact period-one normalization. -/
theorem tendsto_classicalDiscriminant_mass_coefficient (φ : Curve (ℂ × ℂ)) :
    Tendsto (fun y : ℝ => (2*y : ℂ) *
      (exp (-(y : ℂ)) * classicalDiscriminant φ ((y : ℂ)*I) - 1))
      atTop (𝓝 (classicalPhysicalMass φ)) := by
  have heR : Tendsto (fun y : ℝ => (2*y) * Real.exp (-(2*y))) atTop (𝓝 0) := by
    simpa only [pow_one, Function.comp_def, id_eq] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have he : Tendsto (fun y : ℝ => (2*y : ℂ) * exp (-(2*y : ℂ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_exp, Complex.ofReal_neg] using Complex.continuous_ofReal.continuousAt.tendsto.comp heR
  have h := ((tendsto_classicalDiscriminant_massCorrection_remainder φ).add
    (tendsto_classicalUpperMassCorrection_scaled φ)).add he
  simp only [zero_add, add_zero] at h
  convert h using 1
  ext y
  ring

/-- Equal classical discriminants determine the same physical mass. -/
theorem classicalPhysicalMass_eq_of_discriminant_eq (φ ψ : Curve (ℂ × ℂ))
    (h : classicalDiscriminant φ = classicalDiscriminant ψ) :
    classicalPhysicalMass φ = classicalPhysicalMass ψ := by
  have hφ := tendsto_classicalDiscriminant_mass_coefficient φ
  rw [h] at hφ
  exact tendsto_nhds_unique hφ (tendsto_classicalDiscriminant_mass_coefficient ψ)

@[simp] theorem classicalPhysicalMass_const (v : ℂ × ℂ) :
    classicalPhysicalMass (ContinuousMap.const _ v) = v.1 * v.2 := by
  simp [classicalPhysicalMass, NLS.LinearVolterra.extend]

end NLS.ZakharovShabat
