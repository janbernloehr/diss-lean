import NLS.SequenceSpaces.FiniteCenterBall

/-! # Finite centers with no zero head pairs

Removing indices at which both base coordinates vanish does not change a
finite truncation. Thus the finite head of a centered neighborhood can be
chosen so that each retained pair has a nonzero coordinate.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Discard zero coordinate pairs from a finite head. -/
def activeHead (S : Finset ℤ) (z : Coeff p × Coeff p) : Finset ℤ :=
  S.filter fun k => z.1 k ≠ 0 ∨ z.2 k ≠ 0

omit [Fact (1 ≤ p)] in
@[simp] theorem mem_activeHead (S : Finset ℤ) (z : Coeff p × Coeff p) (k : ℤ) :
    k ∈ activeHead S z ↔ k ∈ S ∧ (z.1 k ≠ 0 ∨ z.2 k ≠ 0) := by
  classical
  simp [activeHead]

omit [Fact (1 ≤ p)] in
@[simp] theorem truncatePair_activeHead (S : Finset ℤ) (z : Coeff p × Coeff p) :
    truncatePair (activeHead S z) z = truncatePair S z := by
  apply Prod.ext <;> ext k <;>
    by_cases hk : k ∈ S <;> by_cases hx : z.1 k = 0 <;> by_cases hy : z.2 k = 0 <;>
    simp [truncatePair,hk,hx,hy]

/-- Every open neighborhood admits a finite center with no zero retained
pairs, while still containing the original point in the centered ball. -/
theorem exists_nonzeroFiniteCenter_ball (hp : p ≠ ⊤) (U : Set (Coeff p × Coeff p))
    (hU : IsOpen U) (z : Coeff p × Coeff p) (hz : z ∈ U) :
    ∃ S : Finset ℤ, ∃ R : ℝ, 0 < R ∧ z ∈ ball (truncatePair S z) R ∧
      ball (truncatePair S z) R ⊆ U ∧ ∀ k ∈ S, z.1 k ≠ 0 ∨ z.2 k ≠ 0 := by
  obtain ⟨S,R,hR,hzR,hball⟩ := exists_finiteCenter_ball hp U hU z hz
  refine ⟨activeHead S z,R,hR,?_,?_,?_⟩
  · simpa using hzR
  · simpa using hball
  · intro k hk
    exact (mem_activeHead S z k).mp hk |>.2

end NLS.Coeff
