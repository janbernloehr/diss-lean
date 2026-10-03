import NLS.ZakharovShabat.ClassicalDirichletGradientValueBounds

/-! # Time regularity and the ODE for the normalized Dirichlet gradient

The normalized squared eigenfunction is C¹ in time. Its equation separates
the spectral drift from a bounded potential term. Subtracting the free
gradient cancels the large oscillatory contribution to the error derivative.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The actual normalized physical gradient minus the exact free gradient. -/
def classicalDirichletGradientError (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (t : ℝ) : ℂ × ℂ :=
  classicalDirichletNormalizedGradient Φ z t-classicalDirichletNormalizedGradient 0 w t

theorem contDiff_classicalDirichletNormalizedGradient (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    ContDiff ℝ 1 (classicalDirichletNormalizedGradient Φ z) := by
  have h := contDiff_classicalSolution Φ z (1,1)
  exact ((h.snd.pow 2).div_const _).prodMk ((h.fst.pow 2).div_const _)

theorem contDiff_classicalDirichletGradientError (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    ContDiff ℝ 1 (classicalDirichletGradientError Φ z w) :=
  (contDiff_classicalDirichletNormalizedGradient Φ z).sub (contDiff_classicalDirichletNormalizedGradient 0 w)

/-- The normalized gradient satisfies its signed spectral drift equation,
including the actual bilinear potential term and both component signs. -/
theorem deriv_classicalDirichletNormalizedGradient (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0 : ℝ) 1) :
    deriv (classicalDirichletNormalizedGradient Φ z) t =
      (2*I*z) • ((classicalDirichletNormalizedGradient Φ z t).1,-(classicalDirichletNormalizedGradient Φ z t).2)+
      (2*I*((classicalDirichletEigenfunction Φ z t).1*(classicalDirichletEigenfunction Φ z t).2/
        classicalDirichletNormalization Φ z)) • (-(Φ t).2,(Φ t).1) := by
  have h := hasDerivAt_classicalSolution Φ z (1,1) t
  have hd := ((((HasFDerivAt.hasDerivAt h.snd).pow 2).div_const (classicalDirichletNormalization Φ z)).prodMk
    (((HasFDerivAt.hasDerivAt h.fst).pow 2).div_const (classicalDirichletNormalization Φ z))).deriv
  change deriv (classicalDirichletNormalizedGradient Φ z) t = _ at hd
  rw [hd]
  apply Prod.ext <;> simp only [classicalDirichletNormalizedGradient,classicalDirichletEigenfunction,
    classicalODECoefficient_apply,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul,
    div_eq_mul_inv] <;> dsimp <;> ring

/-- The large spectral factor multiplies only the small gradient error;
the remaining free term is multiplied by the small spectral displacement. -/
theorem deriv_classicalDirichletGradientError (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (t : Icc (0 : ℝ) 1) :
    deriv (classicalDirichletGradientError Φ z w) t =
      (2*I*z) • ((classicalDirichletGradientError Φ z w t).1,-(classicalDirichletGradientError Φ z w t).2)+
      (2*I*(z-w)) • ((classicalDirichletNormalizedGradient 0 w t).1,-(classicalDirichletNormalizedGradient 0 w t).2)+
      (2*I*((classicalDirichletEigenfunction Φ z t).1*(classicalDirichletEigenfunction Φ z t).2/
        classicalDirichletNormalization Φ z)) • (-(Φ t).2,(Φ t).1) := by
  have hΦ := (contDiff_one_iff_deriv.mp (contDiff_classicalDirichletNormalizedGradient Φ z)).1 t
  have h0 := (contDiff_one_iff_deriv.mp (contDiff_classicalDirichletNormalizedGradient 0 w)).1 t
  change deriv (classicalDirichletNormalizedGradient Φ z - classicalDirichletNormalizedGradient 0 w) t = _
  rw [deriv_sub hΦ h0,
    deriv_classicalDirichletNormalizedGradient Φ z t,deriv_classicalDirichletNormalizedGradient 0 w t]
  apply Prod.ext <;> simp only [classicalDirichletGradientError,Prod.fst_add,Prod.snd_add,
    Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
    ContinuousMap.zero_apply,Prod.fst_zero,Prod.snd_zero,mul_zero,neg_zero] <;> ring

/-- The error derivative is controlled by the small value error, the root
shift, and the normalized bilinear potential term. -/
theorem norm_deriv_classicalDirichletGradientError_le (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (t : Icc (0 : ℝ) 1) :
    ‖deriv (classicalDirichletGradientError Φ z w) t‖ ≤
      2*‖z‖*‖classicalDirichletGradientError Φ z w t‖+
      2*‖z-w‖*‖classicalDirichletNormalizedGradient 0 w t‖+
      2*‖classicalDirichletEigenfunction Φ z t‖^2*
        ‖(classicalDirichletNormalization Φ z)⁻¹‖*‖Φ t‖ := by
  let g := classicalDirichletEigenfunction Φ z t
  have hg : ‖g.1‖*‖g.2‖ ≤ ‖g‖^2 := by
    simpa only [pow_two] using mul_le_mul (norm_fst_le g) (norm_snd_le g)
      (norm_nonneg _) (norm_nonneg _)
  rw [deriv_classicalDirichletGradientError]
  calc
    _ ≤ ‖(2*I*z) • ((classicalDirichletGradientError Φ z w t).1,
          -(classicalDirichletGradientError Φ z w t).2)‖+
        ‖(2*I*(z-w)) • ((classicalDirichletNormalizedGradient 0 w t).1,
          -(classicalDirichletNormalizedGradient 0 w t).2)‖+
        ‖(2*I*(g.1*g.2/classicalDirichletNormalization Φ z)) • (-(Φ t).2,(Φ t).1)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = 2*‖z‖*‖classicalDirichletGradientError Φ z w t‖+
        2*‖z-w‖*‖classicalDirichletNormalizedGradient 0 w t‖+
        2*(‖g.1‖*‖g.2‖)*‖(classicalDirichletNormalization Φ z)⁻¹‖*‖Φ t‖ := by
      simp only [norm_smul,norm_mul,Complex.norm_ofNat,Complex.norm_I,mul_one,
        div_eq_mul_inv,Prod.norm_def,norm_neg,max_comm]
      ring
    _ ≤ _ := by gcongr

end NLS.ZakharovShabat
