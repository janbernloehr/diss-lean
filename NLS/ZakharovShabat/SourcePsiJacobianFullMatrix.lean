import NLS.ZakharovShabat.SourcePsiJacobianFullExtension
import NLS.ZakharovShabat.SourcePsiSelectedJacobianEntry
import NLS.SequenceSpaces.FiniteBlockOperatorConvergence

/-!
# Matrix entries of the common-space psi Jacobian

The finite-block operator convergence criterion reads the entries of
the full-space extension on coordinate vectors. On retained rows and
columns these are exactly the scalar contour derivatives already
computed for the selected equation. The deleted row and column have
the fixed block values from the extension construction.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- On a valid selected contour chart, a retained matrix entry of
the full-space psi Jacobian is the scalar directional contour
derivative from Lemma 12.5. -/
theorem sourcePsiFullRootJacobian_retained_entry_eq_deriv
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hcoord : ∀ t ∈ U, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m))
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (m k : ℤ) (hmn : m ≠ n) (hkn : k ≠ n) :
    (sourcePsiFullRootJacobian hp hp1 n c R a ψ
      (lp.single p k 1)) m =
        deriv (fun z : ℂ =>
          sourcePsiDeletedEquationCoordinate hp hp1 n m
            (a + Coeff.deletedSingleCLM n k hkn z) ψ (c m) (R m)) 0 := by
  unfold sourcePsiFullRootJacobian Coeff.deletedJacobianExtension
  rw [Coeff.deletedOperatorExtension_apply_other n m hmn,
    Coeff.deleteCoordinateTo_single_other n k hkn]
  exact sourcePsiSelectedRootJacobian_entry_eq_deletedCoordinate
    hp hp1 n c R U hUopen hcoord hdiff a ψ hpair m k hkn

/-- The deleted output row has no entry in any retained input
column. -/
theorem sourcePsiFullRootJacobian_entry_deleted_row
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hkn : k ≠ n) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) :
    (sourcePsiFullRootJacobian hp hp1 n c R a ψ
      (lp.single p k 1)) n = 0 := by
  rw [sourcePsiFullRootJacobian_deletedRow]
  simp [Ne.symm hkn]

/-- The deleted diagonal entry is exactly two. -/
theorem sourcePsiFullRootJacobian_entry_deleted_diagonal
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) :
    (sourcePsiFullRootJacobian hp hp1 n c R a ψ
      (lp.single p n 1)) n = 2 := by
  rw [sourcePsiFullRootJacobian_deletedRow]
  simp

/-- A retained output row has zero entry in the deleted input
column. -/
theorem sourcePsiFullRootJacobian_entry_deleted_column
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hmn : m ≠ n) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) :
    (sourcePsiFullRootJacobian hp hp1 n c R a ψ
      (lp.single p n 1)) m = 0 := by
  rw [sourcePsiFullRootJacobian_deletedColumn]
  simp [hmn]

end NLS.ZakharovShabat
