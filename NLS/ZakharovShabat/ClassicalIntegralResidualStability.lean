import NLS.ZakharovShabat.ClassicalResidualStability
import NLS.ZakharovShabat.ClassicalEndpointGradientBounds
import NLS.ComplexAnalysis.OscillatoryIntegralL2

/-! # Integral residual stability for the actual spectral solution

Continuous forcing is controlled by its L1 norm, or by its scalar L2 norm, uniformly on horizontal complex spectral strips.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The actual forced solution is bounded by the integral norm of its forcing. -/
theorem norm_classicalForcedKernelSolution_le_integral
    (Φ g : Curve (ℂ × ℂ)) (z : ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hsol : ∀ v : ℂ × ℂ, ‖v‖ ≤ 1 → ∀ t : Icc (0:ℝ) 1,
      ‖classicalSolution Φ z v t‖ ≤ B) (t : Icc (0:ℝ) 1) :
    ‖classicalForcedKernelSolution Φ g z t‖ ≤
      4*B^2*(∫ s in (0:ℝ)..1, ‖extend g s‖) := by
  let D := ∫ s in (0:ℝ)..1, ‖extend g s‖
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg (by norm_num) (fun s _ => norm_nonneg _)
  have hp (u v f q : ℂ) (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B)
      (R : ℝ) (hf : ‖f‖ ≤ R) (hq : ‖q‖ ≤ R) : ‖u*f-v*q‖ ≤ 2*B*R := by
    calc
      _ ≤ ‖u‖*‖f‖+‖v‖*‖q‖ := by simpa only [norm_mul] using norm_sub_le (u*f) (v*q)
      _ ≤ B*R+B*R := add_le_add
        (mul_le_mul hu hf (norm_nonneg _) hB) (mul_le_mul hv hq (norm_nonneg _) hB)
      _ = _ := by ring
  have hpoint (s : Icc (0:ℝ) 1) :
      ‖classicalForcedKernelIntegrand Φ g z s‖ ≤ 2*B*‖g s‖ := by
    have ha := hsol (1,0) (by simp) s
    have hb := hsol (0,1) (by simp) s
    simp only [classicalForcedKernelIntegrand,extend_coe,Prod.norm_def,max_le_iff]
    constructor
    · exact hp _ _ _ _ ((norm_snd_le _).trans hb) ((norm_fst_le _).trans hb) _
        (norm_fst_le _) (norm_snd_le _)
    · rw [show -(classicalSolution Φ z (1,0) s).2*(g s).1+
        (classicalSolution Φ z (1,0) s).1*(g s).2 =
        (classicalSolution Φ z (1,0) s).1*(g s).2-
          (classicalSolution Φ z (1,0) s).2*(g s).1 by ring]
      exact hp _ _ _ _ ((norm_fst_le _).trans ha) ((norm_snd_le _).trans ha) _
        (norm_snd_le _) (norm_fst_le _)
  have hint : ‖classicalForcedKernelPrimitive Φ g z t‖ ≤ 2*B*D := by
    apply (intervalIntegral.norm_integral_le_integral_norm t.property.1).trans
    calc
      _ ≤ ∫ s in (0:ℝ)..t.val, 2*B*‖extend g s‖ := by
        apply intervalIntegral.integral_mono_on t.property.1
          ((continuous_classicalForcedKernelIntegrand Φ g z).norm.intervalIntegrable 0 t)
          ((continuous_const.mul (continuous_extend g).norm).intervalIntegrable 0 t)
        intro s hs
        let q : Icc (0:ℝ) 1 := ⟨s,⟨hs.1,hs.2.trans t.property.2⟩⟩
        change ‖classicalForcedKernelIntegrand Φ g z q‖ ≤ 2*B*‖extend g q‖
        simpa only [extend_coe] using hpoint q
      _ = 2*B*(∫ s in (0:ℝ)..t.val, ‖extend g s‖) := intervalIntegral.integral_const_mul _ _
      _ ≤ 2*B*D := mul_le_mul_of_nonneg_left
        (intervalIntegral.integral_mono_interval le_rfl t.property.1 t.property.2
          (Filter.Eventually.of_forall (fun s => norm_nonneg _))
          ((continuous_extend g).norm.intervalIntegrable 0 1)) (by positivity)
  unfold classicalForcedKernelSolution
  calc
    _ ≤ ‖(classicalForcedKernelPrimitive Φ g z t).1‖*‖classicalSolution Φ z (1,0) t‖+
        ‖(classicalForcedKernelPrimitive Φ g z t).2‖*‖classicalSolution Φ z (0,1) t‖ := by
      simpa only [norm_smul] using norm_add_le
        ((classicalForcedKernelPrimitive Φ g z t).1 • classicalSolution Φ z (1,0) t)
        ((classicalForcedKernelPrimitive Φ g z t).2 • classicalSolution Φ z (0,1) t)
    _ ≤ (2*B*D)*B+(2*B*D)*B := add_le_add
      (mul_le_mul ((norm_fst_le _).trans hint) (hsol _ (by simp) t) (norm_nonneg _) (by positivity))
      (mul_le_mul ((norm_snd_le _).trans hint) (hsol _ (by simp) t) (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- A residual integral controls the actual solution error uniformly on a complex spectral strip. -/
theorem norm_sub_classicalSolution_strip_le_integral_residual
    (Φ g : Curve (ℂ × ℂ)) (z : ℂ) (H : ℝ) (hz : |z.im| ≤ H)
    (u : ℝ → ℂ × ℂ) (hu : Continuous u)
    (hd : ∀ t : Icc (0:ℝ) 1, HasDerivAt u (classicalODECoefficient (Φ t) z (u t)+g t) t)
    (t : Icc (0:ℝ) 1) :
    ‖u t-classicalSolution Φ z (u 0) t‖ ≤
      4*(Real.exp (‖Φ‖+H))^2*(∫ s in (0:ℝ)..1, ‖extend g s‖) := by
  have he := classicalSolution_unique Φ z (u 0)
    (fun s => u s-classicalForcedKernelSolution Φ g z s)
    (hu.sub (continuous_classicalForcedKernelSolution Φ g z)).continuousOn
    (by simp) (fun s _ => by
      have hh := (hd s).sub (hasDerivAt_classicalForcedKernelSolution Φ g z s)
      convert! hh using 1
      simp only [map_sub]
      abel)
  have hv : u t-classicalSolution Φ z (u 0) t = classicalForcedKernelSolution Φ g z t := by
    rw [← he t.property]
    exact sub_sub_cancel _ _
  rw [hv]
  apply norm_classicalForcedKernelSolution_le_integral Φ g z _ (Real.exp_pos _).le _ t
  intro v hv s
  exact norm_classicalSolution_unit_strip_le ‖Φ‖ H Φ le_rfl z hz v hv s

/-- A scalar L2 residual controls the actual solution error without its pointwise supremum. -/
theorem norm_sub_classicalSolution_strip_le_scalarL2_residual
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (H : ℝ) (hz : |z.im| ≤ H)
    (f : ℝ → ℂ) (hf : Continuous f) (hL2 : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (u : ℝ → ℂ × ℂ) (hu : Continuous u)
    (hd : ∀ t : Icc (0:ℝ) 1, HasDerivAt u (classicalODECoefficient (Φ t) z (u t)+(0,f t)) t)
    (t : Icc (0:ℝ) 1) :
    ‖u t-classicalSolution Φ z (u 0) t‖ ≤
      4*(Real.exp (‖Φ‖+H))^2*Real.sqrt (∫ s in (0:ℝ)..1, ‖f s‖^2) := by
  let g : Curve (ℂ × ℂ) := ⟨fun s => (0,f s),continuous_const.prodMk (hf.comp continuous_subtype_val)⟩
  have h := norm_sub_classicalSolution_strip_le_integral_residual Φ g z H hz u hu hd t
  have hg : (∫ s in (0:ℝ)..1, ‖extend g s‖) = ∫ s in (0:ℝ)..1, ‖f s‖ := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    let q : Icc (0:ℝ) 1 := ⟨s,hs⟩
    change ‖extend g q‖ = ‖f q‖
    rw [extend_coe]
    simp only [g,ContinuousMap.coe_mk,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
  rw [hg] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Real.sqrt_one,one_mul] using
    NLS.ComplexAnalysis.integral_norm_le_sqrt_length_mul_L2 f 1 (by norm_num) hL2

end NLS.ZakharovShabat
