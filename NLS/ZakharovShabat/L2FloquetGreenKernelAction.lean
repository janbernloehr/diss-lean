import NLS.ZakharovShabat.L2FloquetKernelCancellation
import NLS.ZakharovShabat.L2WholeLineModeKernelBound
import NLS.ZakharovShabat.L2FloquetInhomogeneous

/-! # The actual projected Green kernels in the original pair coordinates -/
noncomputable section
set_option autoImplicit false
open Matrix Module Complex
namespace NLS.ZakharovShabat

/-- The first root projection selects exactly the first column of its eigenbasis. -/
theorem floquetRootProjection_basis_first (M : Matrix (Fin 2) (Fin 2) ℂ)
    (μ ν : ℂ) (hne : μ ≠ ν) (b : Basis (Fin 2) ℂ (Fin 2 → ℂ))
    (hμ : M *ᵥ b 0 = μ • b 0) (hν : M *ᵥ b 1 = ν • b 1) (j : Fin 2) :
    floquetRootProjection M μ ν *ᵥ b j = if j = 0 then b j else 0 := by
  have h := LinearMap.congr_fun (floquetRootProjection_mulVecLin M μ ν hne b hμ hν) (b j)
  fin_cases j <;> simpa [floquetModeProjection_apply] using h

/-- Reversing the roots selects exactly the second eigenbasis column. -/
theorem floquetRootProjection_basis_second (M : Matrix (Fin 2) (Fin 2) ℂ)
    (μ ν : ℂ) (hne : μ ≠ ν) (b : Basis (Fin 2) ℂ (Fin 2 → ℂ))
    (hμ : M *ᵥ b 0 = μ • b 0) (hν : M *ᵥ b 1 = ν • b 1) (j : Fin 2) :
    floquetRootProjection M ν μ *ᵥ b j = if j = 1 then b j else 0 := by
  fin_cases j
  · simp [floquetRootProjection,Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,hμ]
  · change floquetRootProjection M ν μ *ᵥ b 1 = b 1
    simp only [floquetRootProjection,Matrix.smul_mulVec,Matrix.sub_mulVec,
      Matrix.one_mulVec,hν,← sub_smul,smul_smul,
      inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm),one_smul]

/-- The first physical kernel is the original first scalar propagator times its periodic column. -/
theorem l2FloquetModeKernel_action_first (u : IntervalPairL2) (z μ ν : ℂ)
    (hne : μ ≠ ν) (b : Basis (Fin 2) ℂ (Fin 2 → ℂ))
    (hμ : l2Monodromy u z *ᵥ b 0 = μ • b 0)
    (hν : l2Monodromy u z *ᵥ b 1 = ν • b 1) (t s : ℝ) (v : ℂ × ℂ) :
    wholeLineMatrixAction (l2FloquetModeKernel u z μ ν t s) v =
      (Complex.exp (Complex.log μ*((t-s : ℝ) : ℂ))*
        (wholeLineMatrixAction (l2FloquetPeriodicMatrix u z b ![μ,ν] s)⁻¹ v).1) •
          l2FloquetPeriodicColumn u z (b 0) μ t := by
  have he := l2FloquetPeriodicMatrix_modeKernel u z b ![μ,ν] 0
    (floquetRootProjection (l2Monodromy u z) μ ν)
    (floquetRootProjection_basis_first _ μ ν hne b hμ hν) t s
  change _ = l2FloquetModeKernel u z μ ν t s at he
  rw [← he,← wholeLineMatrixAction_mul,← wholeLineMatrixAction_mul,
    wholeLineMatrixAction_columns]
  change _ = (Complex.exp (Complex.log μ*((t-s : ℝ) : ℂ))*
    (wholeLineMatrixAction (l2FloquetPeriodicMatrix u z b ![μ,ν] s)⁻¹ v).1) •
      (l2FloquetPeriodicMatrix u z b ![μ,ν] t 0 0,l2FloquetPeriodicMatrix u z b ![μ,ν] t 1 0)
  simp [wholeLineMatrixAction]

/-- The reversed physical kernel is the second scalar propagator times its periodic column. -/
theorem l2FloquetModeKernel_action_second (u : IntervalPairL2) (z μ ν : ℂ)
    (hne : μ ≠ ν) (b : Basis (Fin 2) ℂ (Fin 2 → ℂ))
    (hμ : l2Monodromy u z *ᵥ b 0 = μ • b 0)
    (hν : l2Monodromy u z *ᵥ b 1 = ν • b 1) (t s : ℝ) (v : ℂ × ℂ) :
    wholeLineMatrixAction (l2FloquetModeKernel u z ν μ t s) v =
      (Complex.exp (Complex.log ν*((t-s : ℝ) : ℂ))*
        (wholeLineMatrixAction (l2FloquetPeriodicMatrix u z b ![μ,ν] s)⁻¹ v).2) •
          l2FloquetPeriodicColumn u z (b 1) ν t := by
  have he := l2FloquetPeriodicMatrix_modeKernel u z b ![μ,ν] 1
    (floquetRootProjection (l2Monodromy u z) ν μ)
    (floquetRootProjection_basis_second _ μ ν hne b hμ hν) t s
  change _ = l2FloquetModeKernel u z ν μ t s at he
  rw [← he,← wholeLineMatrixAction_mul,← wholeLineMatrixAction_mul,
    wholeLineMatrixAction_columns]
  change _ = (Complex.exp (Complex.log ν*((t-s : ℝ) : ℂ))*
    (wholeLineMatrixAction (l2FloquetPeriodicMatrix u z b ![μ,ν] s)⁻¹ v).2) •
      (l2FloquetPeriodicMatrix u z b ![μ,ν] t 0 1,l2FloquetPeriodicMatrix u z b ![μ,ν] t 1 1)
  simp [wholeLineMatrixAction]

end NLS.ZakharovShabat
