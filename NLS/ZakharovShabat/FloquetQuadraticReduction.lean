import NLS.ZakharovShabat.FloquetHyperbolicRoots
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Characteristic-quadratic reduction without diagonalizability -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace NLS.ZakharovShabat

/-- Applying one characteristic factor produces an eigenvector for the
other root, possibly zero. This remains valid at repeated roots. -/
theorem mulVec_sub_smul_eigenvector_of_two_roots (M : Matrix (Fin 2) (Fin 2) ℂ)
    (μ ν : ℂ) (hsum : M.trace = μ+ν) (hprod : M.det = μ*ν) (v : Fin 2 → ℂ) :
    M *ᵥ (M *ᵥ v-ν • v) = μ • (M *ᵥ v-ν • v) := by
  simp only [Matrix.trace,Fin.sum_univ_two,Matrix.det_fin_two] at hsum hprod
  change M 0 0+M 1 1 = μ+ν at hsum
  funext i
  fin_cases i
  · simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    change M 0 0*(M 0 0*v 0+M 0 1*v 1-ν*v 0)+M 0 1*(M 1 0*v 0+M 1 1*v 1-ν*v 1) =
      μ*(M 0 0*v 0+M 0 1*v 1-ν*v 0)
    linear_combination (M 0 0*v 0+M 0 1*v 1)*hsum-v 0*hprod
  · simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    change M 1 0*(M 0 0*v 0+M 0 1*v 1-ν*v 0)+M 1 1*(M 1 0*v 0+M 1 1*v 1-ν*v 1) =
      μ*(M 1 0*v 0+M 1 1*v 1-ν*v 1)
    linear_combination (M 1 0*v 0+M 1 1*v 1)*hsum-v 1*hprod

/-- Every unimodular quadratic factors into two reciprocal nonzero roots,
without requiring that the roots be distinct. -/
theorem exists_reciprocal_roots_with_sum (d : ℂ) :
    ∃ μ ν : ℂ, μ ≠ 0 ∧ ν ≠ 0 ∧ d = μ+ν ∧ μ*ν = 1 := by
  obtain ⟨μ,hp⟩ := exists_root_floquet_quadratic d
  have hμ := (inverse_root_floquet_quadratic d μ hp).1
  refine ⟨μ,μ⁻¹,hμ,inv_ne_zero hμ,?_,mul_inv_cancel₀ hμ⟩
  field_simp
  linear_combination -hp

end NLS.ZakharovShabat
