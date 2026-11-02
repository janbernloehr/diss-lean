import NLS.Articles.MKdVNLSHierarchies.InitialChecks
import NLS.ZakharovShabat.SobolevHierarchyGradientSymmetries

/-! # Theorem 2(i) on its original complex Sobolev domain

The gradients below are analytic L² fields representing the existing physical
Hamiltonian's Fréchet derivative. The Poisson vector field is exactly -iJ
times this gradient. No smoothness or gradient-identification hypothesis is
assumed by these source interfaces.
-/
noncomputable section
open Complex NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

/-- The source phase rotation acting on physical L² gradient/vector fields. -/
def phaseRotationL2 (α : ℝ) (g : Coeff 2 × Coeff 2) : Coeff 2 × Coeff 2 :=
  (Complex.exp ((α : ℂ)*I) • g.1, Complex.exp (-((α : ℂ)*I)) • g.2)

theorem theorem2_i_swap_gradients (k : ℕ) (hk : 1 ≤ k) (ab : SobolevSource (k-1)) :
    sobolevNLSHierarchyGradient (k-1) k ab = (-1 : ℂ)^(k-1) •
      ((sobolevNLSHierarchyGradient (k-1) k (hierarchyComponentSwap (k-1) ab)).2,
        (sobolevNLSHierarchyGradient (k-1) k (hierarchyComponentSwap (k-1) ab)).1) := by
  have h := sobolevNLSHierarchyGradient_swap (k-1) (k-1) (by omega)
    (hierarchyComponentSwap (k-1) ab)
  simpa only [Nat.sub_add_cancel hk, hierarchyComponentSwap_apply] using h

theorem theorem2_i_phase_gradients (k : ℕ) (hk : 1 ≤ k)
    (ab : SobolevSource (k-1)) (α : ℝ) :
    sobolevNLSHierarchyGradient (k-1) k ab =
      phaseRotationL2 α (sobolevNLSHierarchyGradient (k-1) k (phaseRotation (k-1) α ab)) := by
  have h := sobolevNLSHierarchyGradient_reciprocal_scaling (k-1) k (by omega) ab
    (Complex.exp ((α : ℂ)*I)) (Complex.exp_ne_zero _)
  unfold phaseRotation
  rw [h]
  simp [phaseRotationL2, Complex.exp_neg, smul_smul]

theorem theorem2_i_phase_vector_fields (k : ℕ) (hk : 1 ≤ k)
    (ab : SobolevSource (k-1)) (α : ℝ) :
    sobolevNLSHierarchyVectorField (k-1) k (phaseRotation (k-1) α ab) =
      phaseRotationL2 α (sobolevNLSHierarchyVectorField (k-1) k ab) := by
  simpa only [phaseRotation, phaseRotationL2, Complex.exp_neg] using
    sobolevNLSHierarchyVectorField_reciprocal_scaling (k-1) k (by omega) ab
      (Complex.exp ((α : ℂ)*I)) (Complex.exp_ne_zero _)

theorem theorem2_i_swap_vector_fields (k : ℕ) (hk : 1 ≤ k) (ab : SobolevSource (k-1)) :
    sobolevNLSHierarchyVectorField (k-1) k (hierarchyComponentSwap (k-1) ab) =
      (-1 : ℂ)^k • ((sobolevNLSHierarchyVectorField (k-1) k ab).2,
        (sobolevNLSHierarchyVectorField (k-1) k ab).1) := by
  simpa only [Nat.sub_add_cancel hk] using
    sobolevNLSHierarchyVectorField_swap (k-1) (k-1) (by omega) ab

end NLS.Articles.MKdVNLSHierarchies
