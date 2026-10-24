import NLS.ZakharovShabat.FloquetPeriodicFactor
import NLS.ZakharovShabat.L2WholeLineFloquetMass
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Topology.Instances.Matrix

/-! # A bounded invertible periodic Floquet change of basis -/
noncomputable section
set_option autoImplicit false
open Set Complex Matrix Module
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- Exact signed integer translation for an arbitrary physical Floquet eigenvector. -/
theorem l2WholeLineFundamentalMatrix_mulVec_add_int (u : IntervalPairL2) (z μ : ℂ)
    (hμ : μ ≠ 0) (v : Fin 2 → ℂ) (hv : l2Monodromy u z *ᵥ v = μ • v)
    (t : ℝ) (n : ℤ) :
    l2WholeLineFundamentalMatrix u z (t+n) *ᵥ v =
      μ^n • (l2WholeLineFundamentalMatrix u z t *ᵥ v) := by
  rw [l2WholeLineFundamentalMatrix_add_int,← Matrix.mulVec_mulVec,
    unit_matrix_zpow_mulVec_of_eigenvector (l2MonodromyUnit u z) μ hμ v hv n,
    Matrix.mulVec_smul]

/-- Columns are actual physical Floquet modes with their exponential factors removed. -/
def l2FloquetPeriodicMatrix (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => floquetPeriodicFactor (μ j) (fun s => l2WholeLineFundamentalMatrix u z s *ᵥ b j) t i

/-- Exact matrix factorization of the periodic change of basis. -/
theorem l2FloquetPeriodicMatrix_eq_mul_diagonal (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ) (t : ℝ) :
    l2FloquetPeriodicMatrix u z b μ t =
      l2WholeLineFundamentalMatrix u z t * (Pi.basisFun ℂ (Fin 2)).toMatrix b *
        Matrix.diagonal (fun j => Complex.exp (-(t : ℂ)*Complex.log (μ j))) := by
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [l2FloquetPeriodicMatrix,floquetPeriodicFactor,Pi.smul_apply,smul_eq_mul,
    Matrix.mul_apply,Module.Basis.toMatrix_apply,Pi.basisFun_repr,
    Matrix.mulVec,dotProduct]
  ring

/-- No time loses invertibility, since the original fundamental matrix,
basis matrix and diagonal exponential are all invertible. -/
theorem isUnit_l2FloquetPeriodicMatrix (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ) (t : ℝ) :
    IsUnit (l2FloquetPeriodicMatrix u z b μ t) := by
  rw [l2FloquetPeriodicMatrix_eq_mul_diagonal]
  refine (isUnit_l2WholeLineFundamentalMatrix u z t).mul ?_ |>.mul ?_
  · let := Module.Basis.invertibleToMatrix (Pi.basisFun ℂ (Fin 2)) b
    exact isUnit_of_invertible _
  · apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun j _ => Complex.exp_ne_zero _))

theorem continuous_l2FloquetPeriodicMatrix (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ) :
    Continuous (l2FloquetPeriodicMatrix u z b μ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply i).comp (continuous_floquetPeriodicFactor (μ j) _
    (continuous_matrixCurve_mulVec _ (continuous_l2WholeLineFundamentalMatrix u z) (b j)))

/-- The actual change of basis is one-periodic, including negative times. -/
theorem periodic_l2FloquetPeriodicMatrix (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (hM : ∀ j, l2Monodromy u z *ᵥ b j = μ j • b j) :
    Function.Periodic (l2FloquetPeriodicMatrix u z b μ) 1 := by
  intro t
  ext i j
  apply congrFun (periodic_floquetPeriodicFactor (μ j) (hμ j) _ (fun s => ?_) t) i
  simpa only [Int.cast_one,zpow_one] using
    l2WholeLineFundamentalMatrix_mulVec_add_int u z (μ j) (hμ j) (b j) (hM j) s 1

/-- The inverse is continuous because the determinant never vanishes. -/
theorem continuous_inv_l2FloquetPeriodicMatrix (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ) :
    Continuous (fun t => (l2FloquetPeriodicMatrix u z b μ t)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (continuousAt_matrix_inv _ ?_).comp (continuous_l2FloquetPeriodicMatrix u z b μ).continuousAt
  simpa only [Ring.inverse_eq_inv'] using
    continuousAt_inv₀ ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_l2FloquetPeriodicMatrix u z b μ t)).ne_zero

/-- Both directions of the original periodic change of basis are uniformly bounded. -/
theorem bounded_l2FloquetPeriodicMatrix_and_inverse (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (hM : ∀ j, l2Monodromy u z *ᵥ b j = μ j • b j) :
    ∃ C : ℝ, 0 < C ∧ ∀ t, ‖l2FloquetPeriodicMatrix u z b μ t‖ ≤ C ∧
      ‖(l2FloquetPeriodicMatrix u z b μ t)⁻¹‖ ≤ C := by
  have hp := periodic_l2FloquetPeriodicMatrix u z b μ hμ hM
  have hi : Function.Periodic (fun t => (l2FloquetPeriodicMatrix u z b μ t)⁻¹) 1 := by
    intro t
    exact congrArg Inv.inv (hp t)
  obtain ⟨C,hC,hb⟩ := (hp.isBounded_of_continuous one_ne_zero
    (continuous_l2FloquetPeriodicMatrix u z b μ)).exists_pos_norm_le
  obtain ⟨D,hD,hd⟩ := (hi.isBounded_of_continuous one_ne_zero
    (continuous_inv_l2FloquetPeriodicMatrix u z b μ)).exists_pos_norm_le
  exact ⟨max C D,lt_max_of_lt_left hC,fun t =>
    ⟨(hb _ ⟨t,rfl⟩).trans (le_max_left _ _),(hd _ ⟨t,rfl⟩).trans (le_max_right _ _)⟩⟩

end NLS.ZakharovShabat
