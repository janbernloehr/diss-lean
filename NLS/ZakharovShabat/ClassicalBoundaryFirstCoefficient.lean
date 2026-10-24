import NLS.ZakharovShabat.ClassicalMassCorrection
import NLS.ZakharovShabat.ClassicalSpatialReflection
import NLS.ZakharovShabat.ClassicalSeparatedHalfPlaneAsymptotics
import NLS.ComplexAnalysis.ExponentialVolterraApproximation

/-! # The physical first coefficient of the boundary quotient

Exponential Volterra approximation recovers the two endpoint potential
values from the weighted off-diagonal monodromy entries. This identifies
the first Dirichlet/Neumann quotient coefficient on the positive imaginary axis.
-/
noncomputable section
open Set Complex MeasureTheory intervalIntegral Filter Topology
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

theorem norm_classicalWeightedSolution_upper_first_iterate_error (φ : Curve (ℂ × ℂ))
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

/-- The lower weighted monodromy entry recovers the second potential at the endpoint. -/
theorem tendsto_classicalMonodromy_lower_first_coefficient (φ : Curve (ℂ × ℂ)) :
    Tendsto (fun y : ℝ => (2*y : ℂ) * exp (-(y : ℂ)) *
      classicalMonodromy φ ((y : ℂ)*I) 1 0) atTop
      (𝓝 (-I * (φ ⟨1,by norm_num⟩).2)) := by
  let q : ℝ → ℂ := fun r => -I * (NLS.LinearVolterra.extend φ r).2
  have hq : Continuous q := continuous_const.mul (continuous_extend φ).snd
  have hlim := (tendsto_scaled_exponentialVolterra hq 1 (by norm_num)).comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have herr : Tendsto (fun y : ℝ => (2*y : ℂ) *
      ((classicalWeightedSolution φ ((y : ℂ)*I) (I*((y : ℂ)*I)) (1,0) 1).2 -
        exponentialVolterra (-(2*y : ℝ)) q 1)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      ((tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).const_div_atTop (2*‖φ‖^3))
    filter_upwards [eventually_gt_atTop (0 : ℝ),eventually_ge_atTop (‖φ‖^2)] with y hy hlarge
    have hb := norm_classicalWeightedSolution_upper_first_iterate_error φ ((y : ℂ)*I)
      (by simpa using hy) (by simpa using hlarge) ⟨1,by norm_num⟩
    have he : 2*I*((y : ℂ)*I) = (-(2*y : ℝ) : ℂ) := by
      push_cast
      calc
        _ = (2*y : ℂ)*(I*I) := by ring
        _ = _ := by rw [I_mul_I]; ring
    rw [he] at hb
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,
      Complex.ofReal_im,Complex.I_re,mul_zero,add_zero] at hb
    have hn : ‖(2*y : ℂ)‖ = 2*y := by
      rw [show (2*y : ℂ) = ((2*y : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 2*y)]
    rw [norm_mul,hn]
    calc
      _ ≤ (2*y)*(2*‖φ‖^3/(2*y)^2) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2*‖φ‖^3/(2*y) := by field_simp
  have h := herr.add hlim
  simp only [zero_add] at h
  convert! h using 1
  · ext y
    have he : I*((y : ℂ)*I) = -(y : ℂ) := by
      calc
        _ = (y : ℂ)*(I*I) := by ring
        _ = _ := by rw [I_mul_I]; ring
    simp only [Function.comp_apply,id_eq,Complex.ofReal_mul,Complex.ofReal_ofNat,
      classicalWeightedSolution,Prod.smul_snd,smul_eq_mul,Complex.ofReal_one,mul_one,
      classicalMonodromy,classicalFundamentalMatrix,Matrix.of_apply,Matrix.cons_val_one,
      Matrix.cons_val_zero,Matrix.cons_val_fin_one,he]
    ring
  · simp [q,NLS.LinearVolterra.extend]

/-- Reflection recovers the first potential at the initial endpoint from the upper entry. -/
theorem tendsto_classicalMonodromy_upper_first_coefficient (φ : Curve (ℂ × ℂ)) :
    Tendsto (fun y : ℝ => (2*y : ℂ) * exp (-(y : ℂ)) *
      classicalMonodromy φ ((y : ℂ)*I) 0 1) atTop
      (𝓝 (I * (φ ⟨0,by norm_num⟩).1)) := by
  have h := (tendsto_classicalMonodromy_lower_first_coefficient
    (classicalSpatialReflection φ)).neg
  simpa only [classicalMonodromy_spatialReflection,Matrix.of_apply,Matrix.cons_val_one,
    Matrix.cons_val_zero,Matrix.cons_val_fin_one,mul_neg,neg_neg,
    classicalSpatialReflection_apply,sub_self,Prod.snd_swap,neg_mul] using h

/-- The actual boundary quotient has first coefficient minus the endpoint potential sum. -/
theorem tendsto_classicalBoundaryRatio_first_coefficient (φ : Curve (ℂ × ℂ)) :
    Tendsto (fun y : ℝ => ((y : ℂ)*I) *
      (classicalSeparatedCharacteristic .dirichlet φ ((y : ℂ)*I) /
        classicalSeparatedCharacteristic .neumann φ ((y : ℂ)*I) - 1)) atTop
      (𝓝 (-((φ ⟨0,by norm_num⟩).1 + (φ ⟨1,by norm_num⟩).2))) := by
  have hnum := ((tendsto_classicalMonodromy_lower_first_coefficient φ).sub
    (tendsto_classicalMonodromy_upper_first_coefficient φ)).div_const I
  have hden := tendsto_classicalSeparated_upper_normalized .neumann φ
    (fun y : ℝ => (y : ℂ)*I) (by simpa using! (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))
  have hden' : Tendsto (fun y : ℝ => exp (-(y : ℂ)) *
      classicalSeparatedCharacteristic .neumann φ ((y : ℂ)*I)) atTop (𝓝 (-1/(2*I))) := by
    convert hden using 1
    ext y
    congr 2
    ring_nf
    simp [I_sq]
  have h := (hnum.div hden' (by norm_num : (-1/(2*I) : ℂ) ≠ 0)).const_mul (I/2)
  have hne : ∀ᶠ y : ℝ in atTop, classicalSeparatedCharacteristic .neumann φ ((y : ℂ)*I) ≠ 0 := by
    filter_upwards [hden'.eventually_ne (by norm_num : (-1/(2*I) : ℂ) ≠ 0)] with y hy
    exact fun hz => hy (by rw [hz,mul_zero])
  have he : I/2 * ((-I*(φ ⟨1,by norm_num⟩).2 - I*(φ ⟨0,by norm_num⟩).1)/I/(-1/(2*I))) =
      -((φ ⟨0,by norm_num⟩).1 + (φ ⟨1,by norm_num⟩).2) := by
    field_simp
    ring_nf
    simp [I_sq]
    ring
  rw [he] at h
  apply Tendsto.congr' _ h
  filter_upwards [hne] with y hy
  have hdiff : classicalSeparatedCharacteristic .dirichlet φ ((y : ℂ)*I) -
      classicalSeparatedCharacteristic .neumann φ ((y : ℂ)*I) =
      (classicalMonodromy φ ((y : ℂ)*I) 1 0 - classicalMonodromy φ ((y : ℂ)*I) 0 1)/I := by
    simp only [classicalSeparatedCharacteristic,BoundaryCondition.extensionSign]
    ring
  dsimp only [Pi.div_apply]
  rw [div_sub_one hy,hdiff]
  field_simp [hy,exp_ne_zero]

end NLS.ZakharovShabat
