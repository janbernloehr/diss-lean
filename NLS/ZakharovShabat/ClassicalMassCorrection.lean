import NLS.ZakharovShabat.ClassicalTraceHalfPlaneBounds
import NLS.ComplexAnalysis.ExponentialVolterra

/-! # Isolating the quadratic mass correction to the upper trace

The first nontrivial Volterra iterate is explicit in the potential. Its
error in the normalized discriminant is bounded by a constant times the
inverse square of the imaginary height, uniformly in the real part.
-/
noncomputable section
open Set Complex MeasureTheory intervalIntegral
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The quadratic term that will recover the physical mass at high energy. -/
def classicalUpperMassCorrection (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) : ℂ :=
  ∫ s in 0..t, (NLS.LinearVolterra.extend φ s).1 *
    exponentialVolterra (2*I*z) (fun r => (NLS.LinearVolterra.extend φ r).2) s

private theorem upper_fast_first_iterate_error (φ : Curve (ℂ × ℂ))
    (z : ℂ) (hz : 0 < z.im) (hlarge : ‖φ‖^2 ≤ z.im) (t : Icc (0 : ℝ) 1) :
    ‖(classicalWeightedSolution φ z (I*z) (1,0) t).2 -
      exponentialVolterra (2*I*z) (fun r => -I * (NLS.LinearVolterra.extend φ r).2) t‖ ≤
      2*‖φ‖^3/(2*z.im)^2 := by
  let u := fun r => (classicalWeightedSolution φ z (I*z) (1,0) r).1
  let q := fun r => -I * (NLS.LinearVolterra.extend φ r).2
  have hu : Continuous u := (continuous_classicalWeightedSolution φ z (I*z) (1,0)).fst
  have hq : Continuous q := continuous_const.mul (continuous_extend φ).snd
  have hv := classicalWeightedSolution_upper_snd φ z (1,0) t
  simp only [mul_zero, zero_add] at hv
  rw [hv]
  change ‖exponentialVolterra (2*I*z) (fun r => q r * u r) t -
    exponentialVolterra (2*I*z) q t‖ ≤ _
  rw [← exponentialVolterra_sub (2*I*z) (f := fun r => q r * u r) (hq.mul hu) hq t.val]
  have hb : ∀ r ∈ Icc 0 t.val, ‖q r * u r - q r‖ ≤ ‖φ‖ * (2*‖φ‖^2/(2*z.im)) := by
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1, hr.2.trans t.property.2⟩
    have hslow := (classicalWeightedSolution_upper_bounds φ z hz hlarge (1,0) ⟨r,hr'⟩).2.1
    simp only [norm_one, norm_zero, mul_zero, zero_div, add_zero, mul_one, zero_add] at hslow
    have hslow' : ‖u r - 1‖ ≤ 2*‖φ‖^2/(2*z.im) := by convert hslow using 1; ring
    have hqr : ‖q r‖ ≤ ‖φ‖ := by
      dsimp [q]
      rw [norm_mul, norm_neg, norm_I, one_mul]
      exact (norm_snd_le _).trans (φ.norm_coe_le_norm _)
    rw [← mul_sub_one, norm_mul]
    exact mul_le_mul hqr hslow' (norm_nonneg _) (norm_nonneg _)
  have he := norm_exponentialVolterra_le (2*I*z) (2*z.im) t.val
    (‖φ‖ * (2*‖φ‖^2/(2*z.im))) (by positivity) t.property.1 (by positivity)
    (by simp [Complex.mul_re]) _ hb
  convert he using 1; ring

/-- Removing the explicit quadratic correction leaves an inverse-square error
in the slow diagonal entry of the weighted fundamental solution. -/
theorem norm_classicalWeightedSolution_upper_sub_massCorrection_le
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (hz : 0 < z.im) (hlarge : ‖φ‖^2 ≤ z.im)
    (t : Icc (0 : ℝ) 1) :
    ‖(classicalWeightedSolution φ z (I*z) (1,0) t).1 - 1 -
      classicalUpperMassCorrection φ z t‖ ≤ 2*‖φ‖^4/(2*z.im)^2 := by
  let v := fun r => (classicalWeightedSolution φ z (I*z) (1,0) r).2
  let q := fun r => -I * (NLS.LinearVolterra.extend φ r).2
  have hv : Continuous v := (continuous_classicalWeightedSolution φ z (I*z) (1,0)).snd
  have hq : Continuous q := continuous_const.mul (continuous_extend φ).snd
  have hφ := continuous_extend φ
  have hcorr : classicalUpperMassCorrection φ z t =
      ∫ r in 0..t.val, I * (NLS.LinearVolterra.extend φ r).1 * exponentialVolterra (2*I*z) q r := by
    unfold classicalUpperMassCorrection
    apply intervalIntegral.integral_congr
    intro r _
    dsimp [q]
    rw [exponentialVolterra_const_mul]
    have hI := Complex.I_mul_I
    linear_combination (NLS.LinearVolterra.extend φ r).1 *
      exponentialVolterra (2*I*z) (fun s => (NLS.LinearVolterra.extend φ s).2) r * hI
  rw [classicalWeightedSolution_upper_fst, add_sub_cancel_left, hcorr]
  rw [← intervalIntegral.integral_sub
    (f := fun r => I * (NLS.LinearVolterra.extend φ r).1 * v r)
    (g := fun r => I * (NLS.LinearVolterra.extend φ r).1 * exponentialVolterra (2*I*z) q r)
    ((continuous_const.mul hφ.fst).mul hv |>.intervalIntegrable 0 t.val)
    ((continuous_const.mul hφ.fst).mul (continuous_exponentialVolterra (2*I*z) hq) |>.intervalIntegrable 0 t.val)]
  have hb := norm_integral_mul_le_of_decay
    (fun r => I * (NLS.LinearVolterra.extend φ r).1)
    (fun r => v r - exponentialVolterra (2*I*z) q r) 1 t.val ‖φ‖ 0
    (2*‖φ‖^3/(2*z.im)^2) (by norm_num) t.property (norm_nonneg _) (by norm_num) (by positivity)
    (by
      intro r _
      rw [norm_mul, norm_I, one_mul]
      exact (norm_fst_le _).trans (φ.norm_coe_le_norm _))
    (by
      intro r hr
      simpa only [mul_zero, zero_add] using
        upper_fast_first_iterate_error φ z hz hlarge ⟨r, hr.1, hr.2.trans t.property.2⟩)
  simp only [zero_div, zero_add] at hb
  convert hb using 1
  · congr 1
    apply intervalIntegral.integral_congr
    intro r _
    dsimp [v]
    ring
  · ring

/-- The actual normalized trace has an explicit quadratic correction and an
inverse-square error, with no bound assumed on the solution itself. -/
theorem norm_classicalDiscriminant_upper_sub_massCorrection_le
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (hz : 0 < z.im) (hlarge : ‖φ‖^2 ≤ z.im) :
    ‖exp (I*z) * classicalDiscriminant φ z - (1 + exp (2*I*z)) -
      classicalUpperMassCorrection φ z 1‖ ≤ (2*‖φ‖^4 + 2*‖φ‖^2)/(2*z.im)^2 := by
  let t : Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
  have h₁ := norm_classicalWeightedSolution_upper_sub_massCorrection_le φ z hz hlarge t
  have h₂ := (classicalWeightedSolution_upper_bounds φ z hz hlarge (0,1) t).2.2
  have he : exp (I*z) * classicalDiscriminant φ z - (1 + exp (2*I*z)) -
      classicalUpperMassCorrection φ z 1 =
      ((classicalWeightedSolution φ z (I*z) (1,0) 1).1 - 1 - classicalUpperMassCorrection φ z 1) +
      ((classicalWeightedSolution φ z (I*z) (0,1) 1).2 - exp (2*I*z)) := by
    rw [classicalWeightedSolution_trace]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  convert add_le_add h₁ h₂ using 1 <;>
    simp only [t, norm_zero, norm_one, zero_add,
      mul_one, Complex.ofReal_one]
  ring

end NLS.ZakharovShabat
