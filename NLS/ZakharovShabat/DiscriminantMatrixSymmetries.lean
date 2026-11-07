import NLS.ZakharovShabat.DiscriminantFloquetAlgebra

/-! # Exact gradient and scalar transport algebra under the physical gauges -/
noncomputable section
open Complex Matrix
namespace NLS.ZakharovShabat

def componentSwapMatrix (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![M 1 1,-M 1 0;-M 0 1,M 0 0]

def reciprocalScalingMatrix (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![M 0 0,c*M 0 1;c⁻¹*M 1 0,M 1 1]

def spatialReflectionMonodromyMatrix (T : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![T 0 0,-T 1 0;-T 0 1,T 1 1]

def spatialReflectionFundamentalMatrix (T M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![M 1 1*T 0 0-M 1 0*T 0 1,M 1 0*T 1 1-M 1 1*T 1 0;
     M 0 1*T 0 0-M 0 0*T 0 1,M 0 0*T 1 1-M 0 1*T 1 0]

theorem discriminantGradientMatrix_componentSwap (T M : Matrix (Fin 2) (Fin 2) ℂ) :
    discriminantGradientMatrix (componentSwapMatrix T) (componentSwapMatrix M) =
      (discriminantGradientMatrix T M).swap := by
  apply Prod.ext <;> simp [discriminantGradientMatrix,discriminantGradientState,componentSwapMatrix] <;> ring

theorem discriminantXiMatrix_componentSwap (T M : Matrix (Fin 2) (Fin 2) ℂ) :
    discriminantXiMatrix (componentSwapMatrix T) (componentSwapMatrix M) =
      -discriminantXiMatrix T M := by
  simp [discriminantXiMatrix,discriminantXiState,componentSwapMatrix]
  ring

theorem discriminantGradientMatrix_reciprocalScaling (c : ℂ) (hc : c ≠ 0)
    (T M : Matrix (Fin 2) (Fin 2) ℂ) :
    discriminantGradientMatrix (reciprocalScalingMatrix c T) (reciprocalScalingMatrix c M) =
      (c⁻¹*(discriminantGradientMatrix T M).1,c*(discriminantGradientMatrix T M).2) := by
  apply Prod.ext <;> simp [discriminantGradientMatrix,discriminantGradientState,reciprocalScalingMatrix]
  · field_simp
  · field_simp

theorem discriminantXiMatrix_reciprocalScaling (c : ℂ) (hc : c ≠ 0)
    (T M : Matrix (Fin 2) (Fin 2) ℂ) :
    discriminantXiMatrix (reciprocalScalingMatrix c T) (reciprocalScalingMatrix c M) =
      discriminantXiMatrix T M := by
  simp [discriminantXiMatrix,discriminantXiState,reciprocalScalingMatrix]
  field_simp

theorem discriminantGradientMatrix_spatialReflection (T M : Matrix (Fin 2) (Fin 2) ℂ) :
    discriminantGradientMatrix (spatialReflectionMonodromyMatrix T) (spatialReflectionFundamentalMatrix T M) =
      T.det • (discriminantGradientMatrix T M).swap := by
  apply Prod.ext <;> simp [discriminantGradientMatrix,discriminantGradientState,
    spatialReflectionMonodromyMatrix,spatialReflectionFundamentalMatrix,Matrix.det_fin_two,smul_eq_mul] <;> ring

theorem discriminantXiMatrix_spatialReflection (T M : Matrix (Fin 2) (Fin 2) ℂ) :
    discriminantXiMatrix (spatialReflectionMonodromyMatrix T) (spatialReflectionFundamentalMatrix T M) =
      T.det*discriminantXiMatrix T M := by
  simp [discriminantXiMatrix,discriminantXiState,spatialReflectionMonodromyMatrix,
    spatialReflectionFundamentalMatrix,Matrix.det_fin_two]
  ring

end NLS.ZakharovShabat
