import NLS.SequenceSpaces.WeightedNonnegativeActions
import NLS.SequenceSpaces.RealCoefficientCoordinates

/-! # The real part of the original weighted sequence space

The real space is the closed subspace of sequences with real raw coefficients,
with the inherited weighted norm. Positive weighting identifies it with real lp.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS
namespace WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Reality of the original, unweighted coefficient values. -/
def realLocus : Set (WeightedCoeff w p) := {a | ∀ n, (a.val n).im = 0}

omit [Fact (1 ≤ p)] in
/-- Positive real weighting preserves and reflects reality. -/
theorem mem_realLocus_iff (a : WeightedCoeff w p) :
    a ∈ realLocus w p ↔ weightEquiv w p a ∈ Coeff.realLocus p := by
  constructor
  · intro ha n
    simp only [weightEquiv_apply,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero,ha n,mul_zero]
  · intro ha n
    have hn := ha n
    simp only [weightEquiv_apply,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero] at hn
    exact (mul_eq_zero.mp hn).resolve_left (ne_of_gt (w.positive n))

/-- The closed real linear subspace of the original weighted complex space. -/
abbrev realSubmodule := Coeff.coordinateRealSubmodule (weightIsometry w p).toContinuousLinearEquiv

/-- The submodule has exactly the real raw coefficient values. -/
theorem mem_realSubmodule_iff (a : WeightedCoeff w p) :
    a ∈ realSubmodule w p ↔ a ∈ realLocus w p := by
  rw [Coeff.mem_coordinateRealSubmodule]
  exact (mem_realLocus_iff w p a).symm

theorem isClosed_realSubmodule : IsClosed (realSubmodule w p : Set (WeightedCoeff w p)) :=
  Coeff.isClosed_coordinateRealSubmodule _

end WeightedCoeff

/-- Real sequences with the original weighted norm, as a closed real subspace. -/
abbrev WeightedRealCoeff (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  ↥(WeightedCoeff.realSubmodule w p)

namespace WeightedRealCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

instance : CompleteSpace (WeightedRealCoeff w p) :=
  (WeightedCoeff.isClosed_realSubmodule w p).completeSpace_coe

/-- Inclusion into the original weighted complex space. -/
abbrev complexCLM : WeightedRealCoeff w p →L[ℝ] WeightedCoeff w p :=
  (WeightedCoeff.realSubmodule w p).subtypeL

/-- A real weighted sequence has real raw coefficients. -/
theorem im_eq_zero (a : WeightedRealCoeff w p) (n : ℤ) : (a.val.val n).im = 0 :=
  ((WeightedCoeff.mem_realSubmodule_iff w p a.val).mp a.property) n

/-- Real lp coordinates for the actual weighted real sequence space. -/
abbrev weightEquiv : WeightedRealCoeff w p ≃L[ℝ] RealCoeff p :=
  Coeff.coordinateRealEquiv (WeightedCoeff.weightIsometry w p).toContinuousLinearEquiv

end WeightedRealCoeff
namespace WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Real-part projection in the original weighted space. -/
abbrev reCLM : WeightedCoeff w p →L[ℝ] WeightedRealCoeff w p :=
  Coeff.coordinateReCLM (weightIsometry w p).toContinuousLinearEquiv

/-- Projection followed by inclusion recovers every real weighted sequence. -/
theorem complexCLM_reCLM (a : WeightedCoeff w p) (ha : a ∈ realLocus w p) :
    WeightedRealCoeff.complexCLM w p (reCLM w p a) = a :=
  Coeff.val_coordinateReCLM _ a ((mem_realLocus_iff w p a).mp ha)

end WeightedCoeff
end NLS
