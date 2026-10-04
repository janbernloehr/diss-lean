import NLS.ZakharovShabat.ClassicalForcedKernel
import NLS.ZakharovShabat.ClassicalHorizontalStripBounds

/-! # Stability of the actual spectral initial-value problem

The adjugate variation-of-constants formula bounds a solution error by
its forcing and uniform bounds on the two true fundamental columns.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

private theorem norm_two_products_sub_le (u v f g : ℂ) (B D : ℝ)
    (hB : 0 ≤ B) (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) (hf : ‖f‖ ≤ D) (hg : ‖g‖ ≤ D) :
    ‖u*f-v*g‖ ≤ 2*B*D := by
  calc
    _ ≤ ‖u‖*‖f‖+‖v‖*‖g‖ := by simpa only [norm_mul] using norm_sub_le (u*f) (v*g)
    _ ≤ B*D+B*D := add_le_add
      (mul_le_mul hu hf (norm_nonneg f) hB) (mul_le_mul hv hg (norm_nonneg g) hB)
    _ = _ := by ring

/-- The exact zero-initial forced solution is bounded by the column and
forcing bounds; no spectral-parameter norm enters the constant. -/
theorem norm_classicalForcedKernelSolution_le (Φ g : Curve (ℂ × ℂ)) (z : ℂ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hsol : ∀ v : ℂ × ℂ, ‖v‖ ≤ 1 → ∀ t : Icc (0 : ℝ) 1, ‖classicalSolution Φ z v t‖ ≤ B)
    (hg : ∀ t : Icc (0 : ℝ) 1, ‖g t‖ ≤ D) (t : Icc (0 : ℝ) 1) :
    ‖classicalForcedKernelSolution Φ g z t‖ ≤ 4*B^2*D := by
  have hint (s : Icc (0 : ℝ) 1) : ‖classicalForcedKernelIntegrand Φ g z s‖ ≤ 2*B*D := by
    have ha := hsol (1,0) (by simp) s
    have hb := hsol (0,1) (by simp) s
    have hfst := (norm_fst_le (g s)).trans (hg s)
    have hsnd := (norm_snd_le (g s)).trans (hg s)
    simp only [classicalForcedKernelIntegrand,extend_coe,Prod.norm_def,max_le_iff]
    constructor
    · exact norm_two_products_sub_le _ _ _ _ B D hB
        ((norm_snd_le _).trans hb) ((norm_fst_le _).trans hb) hfst hsnd
    · rw [show -(classicalSolution Φ z (1,0) s).2*(g s).1+
        (classicalSolution Φ z (1,0) s).1*(g s).2 =
        (classicalSolution Φ z (1,0) s).1*(g s).2-(classicalSolution Φ z (1,0) s).2*(g s).1 by ring]
      exact norm_two_products_sub_le _ _ _ _ B D hB
        ((norm_fst_le _).trans ha) ((norm_snd_le _).trans ha) hsnd hfst
  have hprim : ‖classicalForcedKernelPrimitive Φ g z t‖ ≤ 2*B*D := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t.val)
      (f := classicalForcedKernelIntegrand Φ g z) (C := 2*B*D) (by
        intro s hs
        rw [uIoc_of_le t.property.1] at hs
        exact hint ⟨s,⟨hs.1.le,hs.2.trans t.property.2⟩⟩)
    simp only [sub_zero,abs_of_nonneg t.property.1] at hi
    exact hi.trans (mul_le_of_le_one_right (by positivity) t.property.2)
  unfold classicalForcedKernelSolution
  calc
    _ ≤ ‖(classicalForcedKernelPrimitive Φ g z t).1‖*‖classicalSolution Φ z (1,0) t‖+
        ‖(classicalForcedKernelPrimitive Φ g z t).2‖*‖classicalSolution Φ z (0,1) t‖ := by
      simpa only [norm_smul] using norm_add_le
        ((classicalForcedKernelPrimitive Φ g z t).1 • classicalSolution Φ z (1,0) t)
        ((classicalForcedKernelPrimitive Φ g z t).2 • classicalSolution Φ z (0,1) t)
    _ ≤ (2*B*D)*B+(2*B*D)*B := add_le_add
      (mul_le_mul ((norm_fst_le _).trans hprim) (hsol _ (by simp) t) (norm_nonneg _) (by positivity))
      (mul_le_mul ((norm_snd_le _).trans hprim) (hsol _ (by simp) t) (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- A continuously forced approximate solution stays close to the actual
solution with exactly the same initial vector. -/
theorem norm_sub_classicalSolution_le_of_residual (Φ g : Curve (ℂ × ℂ)) (z : ℂ)
    (u : ℝ → ℂ × ℂ) (hu : Continuous u)
    (hd : ∀ t : Icc (0 : ℝ) 1, HasDerivAt u (classicalODECoefficient (Φ t) z (u t)+g t) t)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hsol : ∀ v : ℂ × ℂ, ‖v‖ ≤ 1 → ∀ t : Icc (0 : ℝ) 1, ‖classicalSolution Φ z v t‖ ≤ B)
    (hg : ∀ t : Icc (0 : ℝ) 1, ‖g t‖ ≤ D) (t : Icc (0 : ℝ) 1) :
    ‖u t-classicalSolution Φ z (u 0) t‖ ≤ 4*B^2*D := by
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
  exact norm_classicalForcedKernelSolution_le Φ g z B D hB hD hsol hg t

/-- Along the real spectral axis the stability constant is uniform in the
spectral parameter. -/
theorem norm_sub_classicalSolution_real_le_of_residual (Φ g : Curve (ℂ × ℂ)) (r : ℝ)
    (u : ℝ → ℂ × ℂ) (hu : Continuous u)
    (hd : ∀ t : Icc (0 : ℝ) 1, HasDerivAt u (classicalODECoefficient (Φ t) r (u t)+g t) t)
    (D : ℝ) (hD : 0 ≤ D) (hg : ∀ t : Icc (0 : ℝ) 1, ‖g t‖ ≤ D) (t : Icc (0 : ℝ) 1) :
    ‖u t-classicalSolution Φ r (u 0) t‖ ≤ 4*(Real.exp ‖Φ‖)^2*D := by
  apply norm_sub_classicalSolution_le_of_residual Φ g r u hu hd _ D (Real.exp_pos _).le hD _ hg t
  intro v hv s
  apply (norm_classicalSolution_le_exp_im Φ r v s).trans
  simp only [ofReal_im,abs_zero,zero_add]
  calc
    _ ≤ 1*Real.exp ‖Φ‖ := by
      apply mul_le_mul hv (Real.exp_le_exp.mpr (mul_le_of_le_one_right (norm_nonneg Φ) s.property.2))
        (Real.exp_pos _).le zero_le_one
    _ = _ := one_mul _

end NLS.ZakharovShabat
