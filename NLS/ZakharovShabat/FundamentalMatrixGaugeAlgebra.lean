import NLS.ZakharovShabat.DiscriminantMatrixSymmetries

/-! # Algebra of the actual constant gauges and reflected fundamental matrices -/
noncomputable section
open Matrix Complex
namespace NLS.ZakharovShabat

theorem componentSwapMatrix_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    componentSwapMatrix (M*N) = componentSwapMatrix M*componentSwapMatrix N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [componentSwapMatrix,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem reciprocalScalingMatrix_mul (c : ℂ) (hc : c ≠ 0) (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    reciprocalScalingMatrix c (M*N) = reciprocalScalingMatrix c M*reciprocalScalingMatrix c N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reciprocalScalingMatrix,Matrix.mul_apply,Fin.sum_univ_two] <;> field_simp

theorem spatialReflectionFundamentalMatrix_floquet (T M : Matrix (Fin 2) (Fin 2) ℂ) :
    spatialReflectionFundamentalMatrix T (M*T)*spatialReflectionMonodromyMatrix T =
      T.det • spatialReflectionFundamentalMatrix T M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spatialReflectionFundamentalMatrix,spatialReflectionMonodromyMatrix,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.det_fin_two,smul_eq_mul] <;> ring

theorem inverse_fin_two_of_det_one (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) :
    T⁻¹ = !![T 1 1,-T 0 1;-T 1 0,T 0 0] := by
  rw [Matrix.inv_def,hT]
  simp only [Ring.inverse_one,one_smul,Matrix.adjugate_fin_two]

theorem spatialReflectionFundamentalMatrix_eq_inverse (T M : Matrix (Fin 2) (Fin 2) ℂ)
    (hT : T.det = 1) :
    spatialReflectionFundamentalMatrix T M = !![0,1;1,0]*M*T⁻¹*!![0,1;1,0] := by
  rw [inverse_fin_two_of_det_one T hT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spatialReflectionFundamentalMatrix,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> ring

theorem componentSwap_spatialReflectionFundamentalMatrix_eq_inverse (T M : Matrix (Fin 2) (Fin 2) ℂ)
    (hT : T.det = 1) :
    componentSwapMatrix (spatialReflectionFundamentalMatrix T M) =
      !![-1,0;0,1]*M*T⁻¹*!![-1,0;0,1] := by
  rw [inverse_fin_two_of_det_one T hT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [componentSwapMatrix,spatialReflectionFundamentalMatrix,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> ring

theorem componentSwapMatrix_eq_conjugate (M : Matrix (Fin 2) (Fin 2) ℂ) :
    componentSwapMatrix M = !![0,1;-1,0]*M*(!![0,1;-1,0] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ := by
  rw [inverse_fin_two_of_det_one _ (by norm_num [Matrix.det_fin_two])]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [componentSwapMatrix,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

theorem reciprocalScalingMatrix_eq_diagonal_conjugate (c : ℂ) (hc : c ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    reciprocalScalingMatrix (c*c) M =
      !![c,0;0,c⁻¹]*M*(!![c,0;0,c⁻¹] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ := by
  have hd : (!![c,0;0,c⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
    simp [Matrix.det_fin_two,hc]
  rw [inverse_fin_two_of_det_one _ hd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reciprocalScalingMatrix,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp

end NLS.ZakharovShabat
