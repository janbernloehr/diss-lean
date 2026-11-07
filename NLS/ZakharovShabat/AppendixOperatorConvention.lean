import NLS.ZakharovShabat.SourceL2WholeLineFundamentalSymmetries
import NLS.Articles.MKdVNLSHierarchies.FullSpectralSymmetries
import NLS.ZakharovShabat.SourceSymmetryCore

/-! # The explicit component-order adapter for page5 and Appendix A

Those displays put phi2 in the upper off-diagonal slot, whereas Section2
puts phi1 there. The displayed Appendix operator is precisely the Section2
operator at P*phi. Its actual fundamental matrix reflects the spectral
parameter, and its actual phase covariance has the inverse phase factor.
-/
noncomputable section
open Set Complex NLS.Articles.MKdVNLSHierarchies
open scoped ENNReal
namespace NLS.ZakharovShabat

def appendixDisplayedOperator (φ f : ℝ → ℂ × ℂ) (x : ℝ) : ℂ × ℂ :=
  physicalOperator (fun t => (φ t).swap) f x

theorem appendixDisplayedOperator_literal (φ f : ℝ → ℂ × ℂ) (x : ℝ) :
    appendixDisplayedOperator φ f x =
      (I*deriv (fun t => (f t).1) x+(φ x).2*(f x).2,
       -I*deriv (fun t => (f t).2) x+(φ x).1*(f x).1) := rfl

theorem appendix_source_physical_fields (φ : CoeffPair 2) (x : ℝ) :
    physicalBase (periodOnePotential (sourceComponentSwap φ)) x =
      (physicalBase (periodOnePotential φ) x).swap := rfl

theorem appendixDisplayedOperator_source_adapter (φ : CoeffPair 2) (f : ℝ → ℂ × ℂ) (x : ℝ) :
    appendixDisplayedOperator (physicalBase (periodOnePotential φ)) f x =
      physicalOperator (physicalBase (periodOnePotential (sourceComponentSwap φ))) f x := rfl

def appendixFundamentalMatrix (φ : CoeffPair 2) (z : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  l2WholeLineFundamentalMatrix (sourcePhysicalL2 (sourceComponentSwap φ)) z x

theorem appendixFundamentalMatrix_adapter (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    appendixFundamentalMatrix φ z x =
      componentSwapMatrix (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) (-z) x) := by
  unfold appendixFundamentalMatrix
  simpa only [neg_neg] using l2WholeLineFundamentalMatrix_sourceComponentSwap φ (-z) x

theorem appendixFundamentalMatrix_phase (φ : CoeffPair 2) (α : ℝ) (z : ℂ) (x : ℝ) :
    appendixFundamentalMatrix (sourcePhaseRotation α φ) z x =
      reciprocalScalingMatrix ((exp ((α:ℂ)*I))⁻¹) (appendixFundamentalMatrix φ z x) := by
  change l2WholeLineFundamentalMatrix
    (sourcePhysicalL2 (sourceComponentSwap (sourceCircleRotation (Circle.exp α) φ))) z x = _
  rw [sourceComponentSwap_circleRotation]
  change l2WholeLineFundamentalMatrix
    (sourcePhysicalL2 (sourceReciprocalScaling ((exp ((α:ℂ)*I))⁻¹) (sourceComponentSwap φ))) z x = _
  exact l2WholeLineFundamentalMatrix_sourceReciprocalScaling _ (inv_ne_zero (exp_ne_zero _)) _ z x

def appendixMonodromy (φ : CoeffPair 2) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  l2Monodromy (sourcePhysicalL2 (sourceComponentSwap φ)) z

theorem appendixFundamentalMatrix_componentSwap (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    appendixFundamentalMatrix (sourceComponentSwap φ) (-z) x =
      componentSwapMatrix (appendixFundamentalMatrix φ z x) := by
  unfold appendixFundamentalMatrix
  exact l2WholeLineFundamentalMatrix_sourceComponentSwap (sourceComponentSwap φ) z x

theorem appendixFundamentalMatrix_midpointReflection (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    appendixFundamentalMatrix (sourceMidpointReflection φ) (-z) x =
      !![-1,0;0,1]*appendixFundamentalMatrix φ z (1-x)*(appendixMonodromy φ z)⁻¹*!![-1,0;0,1] := by
  unfold appendixFundamentalMatrix appendixMonodromy
  rw [sourceComponentSwap_midpointReflection]
  exact l2WholeLineFundamentalMatrix_sourceMidpointReflection (sourceComponentSwap φ) z x

theorem appendixMonodromy_midpointReflection (φ : CoeffPair 2) (z : ℂ) :
    appendixMonodromy (sourceMidpointReflection φ) (-z) =
      !![(appendixMonodromy φ z) 1 1,(appendixMonodromy φ z) 0 1;
         (appendixMonodromy φ z) 1 0,(appendixMonodromy φ z) 0 0] := by
  unfold appendixMonodromy
  rw [sourceComponentSwap_midpointReflection]
  exact l2Monodromy_sourceMidpointReflection (sourceComponentSwap φ) z

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def appendixPeriodicLeft (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) : ℂ :=
  canonicalPeriodicLeft hp hp1 (periodOnePotential (sourceComponentSwap φ)) (periodOnePotential_mem _) n

def appendixPeriodicRight (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) : ℂ :=
  canonicalPeriodicRight hp hp1 (periodOnePotential (sourceComponentSwap φ)) (periodOnePotential_mem _) n

theorem appendix_signed_endpoint_adapter (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) :
    appendixPeriodicLeft hp hp1 φ n =
        -canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) (-n) ∧
    appendixPeriodicRight hp hp1 φ n =
        -canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) (-n) :=
  sourceCanonicalPeriodicEndpoints_componentSwap hp hp1 φ n

end NLS.ZakharovShabat
