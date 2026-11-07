import NLS.Articles.MKdVNLSHierarchies.GradientSymmetries
import NLS.ZakharovShabat.SobolevHierarchyMidpointReflection

/-! # Proposition 11(i) with all three original symmetries

Pure spatial reflection is now included on the exact original H^(k-1)
complex domain, alongside unsigned swap and arbitrary real phase.
-/
noncomputable section
open Complex NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

theorem proposition11_i_reflection_gradients (k : ℕ) (hk : 1 ≤ k)
    (ab : SobolevSource (k-1)) :
    sobolevNLSHierarchyGradient (k-1) k ab = (-1:ℂ)^(k-1) •
      (Coeff.reflection (sobolevNLSHierarchyGradient (k-1) k
        (hierarchyMidpointReflection (k-1) ab)).1,
       Coeff.reflection (sobolevNLSHierarchyGradient (k-1) k
        (hierarchyMidpointReflection (k-1) ab)).2) := by
  have h := sobolevNLSHierarchyGradient_midpointReflection (k-1) (k-1) (by omega)
    (hierarchyMidpointReflection (k-1) ab)
  have ht : hierarchyMidpointReflection (k-1) (hierarchyMidpointReflection (k-1) ab) = ab := by
    simp only [hierarchyMidpointReflection_apply,WeightedCoeff.reflection_reflection]
  simpa only [Nat.sub_add_cancel hk,ht] using h

theorem proposition11_i (k : ℕ) (hk : 1 ≤ k) (ab : SobolevSource (k-1)) (α : ℝ) :
    (sobolevNLSHierarchyGradient (k-1) k ab = (-1:ℂ)^(k-1) •
      ((sobolevNLSHierarchyGradient (k-1) k (hierarchyComponentSwap (k-1) ab)).2,
       (sobolevNLSHierarchyGradient (k-1) k (hierarchyComponentSwap (k-1) ab)).1)) ∧
    (sobolevNLSHierarchyGradient (k-1) k ab = (-1:ℂ)^(k-1) •
      (Coeff.reflection (sobolevNLSHierarchyGradient (k-1) k (hierarchyMidpointReflection (k-1) ab)).1,
       Coeff.reflection (sobolevNLSHierarchyGradient (k-1) k (hierarchyMidpointReflection (k-1) ab)).2)) ∧
    (sobolevNLSHierarchyGradient (k-1) k ab =
      phaseRotationL2 α (sobolevNLSHierarchyGradient (k-1) k (phaseRotation (k-1) α ab))) :=
  ⟨theorem2_i_swap_gradients k hk ab,proposition11_i_reflection_gradients k hk ab,
    theorem2_i_phase_gradients k hk ab α⟩

end NLS.Articles.MKdVNLSHierarchies
