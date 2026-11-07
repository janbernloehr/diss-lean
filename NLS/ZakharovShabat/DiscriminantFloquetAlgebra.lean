import NLS.ZakharovShabat.DiscriminantGradientStateAlgebra

/-! The adjugate gradient and scalar coefficient are invariant under one
actual Floquet step when the monodromy determinant is one. -/
noncomputable section
open Complex Matrix
namespace NLS.ZakharovShabat

def discriminantGradientMatrix (T M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ × ℂ :=
  discriminantGradientState T (M 0 0,M 1 0) (M 0 1,M 1 1)

def discriminantXiMatrix (T M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  discriminantXiState T (M 0 0,M 1 0) (M 0 1,M 1 1)

theorem discriminantGradientMatrix_mul (T M : Matrix (Fin 2) (Fin 2) ℂ) :
    discriminantGradientMatrix T (M*T) = T.det • discriminantGradientMatrix T M := by
  apply Prod.ext <;>
    simp [discriminantGradientMatrix,discriminantGradientState,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.det_fin_two,smul_eq_mul] <;> ring

theorem discriminantXiMatrix_mul (T M : Matrix (Fin 2) (Fin 2) ℂ) :
    discriminantXiMatrix T (M*T) = T.det*discriminantXiMatrix T M := by
  simp [discriminantXiMatrix,discriminantXiState,Matrix.mul_apply,Fin.sum_univ_two,Matrix.det_fin_two]
  ring

end NLS.ZakharovShabat
