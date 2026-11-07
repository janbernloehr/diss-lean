import NLS.ZakharovShabat.L2DiscriminantPointwiseSymmetries
import NLS.Articles.MKdVNLSHierarchies.NonlocalSign

/-! # Complete physical pointwise gradient and corrected xi clauses

These are actual physical L2 gradients, not merely cotangent identities.
Every spatial point on the whole real line and every original complex H0
source is covered. The nonlocal sign uses the literal Section 2 operator.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

theorem theorem6_iii_pointwise (φ : CoeffPair 2) (α : ℝ) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantGradient (sourcePhysicalL2 (sourceComponentSwap φ)) (-z) x =
        (l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z x).swap ∧
    l2WholeLineDiscriminantGradient (sourcePhysicalL2 (sourceMidpointReflection φ)) (-z) x =
        l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z (1-x) ∧
    l2WholeLineDiscriminantGradient (sourcePhysicalL2 (sourcePhaseRotation α φ)) z x =
        ((exp ((α:ℂ)*I))⁻¹*(l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z x).1,
         exp ((α:ℂ)*I)*(l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z x).2) :=
  ⟨l2WholeLineDiscriminantGradient_sourceComponentSwap φ z x,
   l2WholeLineDiscriminantGradient_sourceMidpointReflection φ z x,
   l2WholeLineDiscriminantGradient_sourceReciprocalScaling _ (exp_ne_zero _) φ z x⟩

theorem theorem6_v_xi_symmetries (φ : CoeffPair 2) (α : ℝ) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantXi (sourcePhysicalL2 φ) z x =
        -l2WholeLineDiscriminantXi (sourcePhysicalL2 (sourceComponentSwap φ)) (-z) x ∧
    l2WholeLineDiscriminantXi (sourcePhysicalL2 φ) z x =
        -l2WholeLineDiscriminantXi (sourcePhysicalL2 (sourceMidpointReflection φ)) (-z) (1-x) ∧
    l2WholeLineDiscriminantXi (sourcePhysicalL2 φ) z x =
        l2WholeLineDiscriminantXi (sourcePhysicalL2 (sourcePhaseRotation α φ)) z x := by
  refine ⟨?_,?_,?_⟩
  · rw [l2WholeLineDiscriminantXi_sourceComponentSwap,neg_neg]
  · rw [l2WholeLineDiscriminantXi_sourceMidpointReflection,neg_neg,
      show (1:ℝ)-(1-x)=x by ring]
  · exact (l2WholeLineDiscriminantXi_sourceReciprocalScaling _ (exp_ne_zero _) φ z x).symm

end NLS.Articles.MKdVNLSHierarchies
