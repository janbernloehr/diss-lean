import NLS.ComplexAnalysis.MatrixTaylorMultiplication
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Invariance under invertible formal matrix operations

Left and right multiplication by formal units preserve every finite Taylor
kernel dimension and the order of the formal determinant.
-/

noncomputable section
open Complex PowerSeries Matrix
namespace NLS.ComplexAnalysis

/-- An invertible change of the output equations leaves the Taylor kernel unchanged. -/
theorem ker_matrixTaylorJetMap_unit_mul (U A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ))
    (hU : IsUnit U) (N : ℕ) :
    LinearMap.ker (matrixTaylorJetMap (U*A) N) = LinearMap.ker (matrixTaylorJetMap A N) := by
  rw [matrixTaylorJetMap_mul]
  ext v
  change matrixTaylorJetMap U N (matrixTaylorJetMap A N v) = 0 ↔ matrixTaylorJetMap A N v = 0
  exact (matrixTaylorJetMap_bijective_of_isUnit U hU N).injective.eq_iff' (map_zero _)

/-- An invertible change of the input coefficients transports the finite Taylor kernel. -/
def matrixTaylorKernelMulUnitEquiv (A U : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ))
    (hU : IsUnit U) (N : ℕ) :
    LinearMap.ker (matrixTaylorJetMap (A*U) N) ≃ₗ[ℂ]
      LinearMap.ker (matrixTaylorJetMap A N) := by
  let e := LinearEquiv.ofBijective (matrixTaylorJetMap U N)
    (matrixTaylorJetMap_bijective_of_isUnit U hU N)
  refine
    { toFun := fun v => ⟨e v.val, by
        have hv := v.property
        simpa only [LinearMap.mem_ker, matrixTaylorJetMap_mul, LinearMap.comp_apply, e, LinearEquiv.ofBijective_apply] using hv⟩
      invFun := fun v => ⟨e.symm v.val, by
        rw [LinearMap.mem_ker, matrixTaylorJetMap_mul, LinearMap.comp_apply]
        change matrixTaylorJetMap A N (e (e.symm v.val)) = 0
        rw [e.apply_symm_apply]
        exact v.property⟩
      left_inv := by
        intro v
        apply Subtype.ext
        exact e.symm_apply_apply v.val
      right_inv := by
        intro v
        apply Subtype.ext
        exact e.apply_symm_apply v.val
      map_add' := by
        intro v w
        apply Subtype.ext
        exact e.map_add v.val w.val
      map_smul' := by
        intro c v
        apply Subtype.ext
        exact e.map_smul c v.val }

/-- Invertible formal row and column operations preserve all finite nullities. -/
theorem finrank_ker_matrixTaylorJetMap_units (L A R : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ))
    (hL : IsUnit L) (hR : IsUnit R) (N : ℕ) :
    Module.finrank ℂ (LinearMap.ker (matrixTaylorJetMap (L*A*R) N)) =
      Module.finrank ℂ (LinearMap.ker (matrixTaylorJetMap A N)) := by
  rw [mul_assoc, ker_matrixTaylorJetMap_unit_mul L (A*R) hL]
  exact (matrixTaylorKernelMulUnitEquiv A R hR N).finrank_eq

/-- Formal row and column units do not change the determinant's vanishing order. -/
theorem order_det_units (L A R : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ))
    (hL : IsUnit L) (hR : IsUnit R) : (L*A*R).det.order = A.det.order := by
  rw [Matrix.det_mul, Matrix.det_mul, PowerSeries.order_mul, PowerSeries.order_mul,
    PowerSeries.order_zero_of_unit ((Matrix.isUnit_iff_isUnit_det L).mp hL),
    PowerSeries.order_zero_of_unit ((Matrix.isUnit_iff_isUnit_det R).mp hR), zero_add, add_zero]

end NLS.ComplexAnalysis
