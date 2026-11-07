import NLS.Articles.KdVConvexity.ActionDifferential
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The actual analytic Hamiltonian gradient has a symmetric complex
bilinear derivative matrix. Adding the literal scalar identity retains
symmetry, without any real-axis or finite-support restriction. -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity

theorem actionGradient_derivative_apply (H : ActionSpace → ℂ) (a v : ActionSpace)
    (hH : AnalyticAt ℂ H a) (n : ℕ+) :
    fderiv ℂ (actionGradient H) a v n=fderiv ℂ (fderiv ℂ H) a v (lp.single 2 n 1) := by
  have hd := (actionCotangentCoefficients.hasFDerivAt.comp a hH.fderiv.differentiableAt.hasFDerivAt).fderiv
  have he : fderiv ℂ (actionGradient H) a v=actionCotangentCoefficients (fderiv ℂ (fderiv ℂ H) a v) :=
    congrArg (fun L : ActionSpace →L[ℂ] ActionSpace => L v) hd
  rw [he,actionCotangentCoefficients_apply]

theorem actionGradient_corrected_matrix_symmetric (H : ActionSpace → ℂ) (a : ActionSpace)
    (hH : AnalyticAt ℂ H a) (c : ℂ) (i j : ℕ+) :
    (fderiv ℂ (actionGradient H) a+c • ContinuousLinearMap.id ℂ ActionSpace) (lp.single 2 j 1) i=
      (fderiv ℂ (actionGradient H) a+c • ContinuousLinearMap.id ℂ ActionSpace) (lp.single 2 i 1) j := by
  have hs : fderiv ℂ (actionGradient H) a (lp.single 2 j 1) i=
      fderiv ℂ (actionGradient H) a (lp.single 2 i 1) j := by
    rw [actionGradient_derivative_apply H a _ hH,actionGradient_derivative_apply H a _ hH]
    exact (hH.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num) _ _
  simp only [add_apply,smul_apply,ContinuousLinearMap.id_apply,lp.coeFn_add,Pi.add_apply,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  rw [hs]
  congr 1
  simp [lp.single_apply,Pi.single_apply,eq_comm]

end NLS.Articles.KdVConvexity
