import NLS.SequenceSpaces.DeletedDiagonal
import NLS.SequenceSpaces.CompactPuncturedKernel

/-!
# Diagonal plus compact decomposition of a deleted-coordinate Jacobian

This packages the operator-theoretic conclusion of Lemma 12.6. The
analytic work still required for the psi Jacobian is expressed as a
uniform diagonal lower bound and an off-diagonal reciprocal entry
estimate with one `ℓᵖ` majorant.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Under the matrix estimates of Lemma 12.5, a bounded Jacobian is
the sum of a diagonal Banach-space isomorphism and a compact operator. -/
theorem deletedJacobian_diagonal_plus_compact
    (hp : p ≠ ⊤) (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (d : Coeff ⊤) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ m : ℤ, m ≠ n → c ≤ ‖d m‖)
    (b : Coeff p) (k : ℤ → Coeff q)
    (hrow : ∀ (m : ℤ) (a : DeletedCoeff p n),
      ((Q a : DeletedCoeff p n) : Coeff p) m =
        d m * (a : Coeff p) m + dualPairing (a : Coeff p) (k m))
    (hdiag : ∀ m : ℤ, k m m = 0)
    (hoff : ∀ m r : ℤ, r ≠ m →
      ‖k m r‖ ≤ ‖b m‖ / |((r - m : ℤ) : ℝ)|) :
    ∃ D K : DeletedCoeff p n →L[ℂ] DeletedCoeff p n,
      Function.Bijective D ∧ IsCompactOperator K ∧ Q = D + K ∧
        (∀ (m : ℤ) (a : DeletedCoeff p n),
          ((D a : DeletedCoeff p n) : Coeff p) m =
            d m * (a : Coeff p) m) := by
  let D : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    deletedMultiplierCLM n d
  let K : DeletedCoeff p n →L[ℂ] DeletedCoeff p n := Q - D
  have hKrow (m : ℤ) (a : DeletedCoeff p n) :
      ((K a : DeletedCoeff p n) : Coeff p) m =
        dualPairing (a : Coeff p) (k m) := by
    calc
      ((K a : DeletedCoeff p n) : Coeff p) m =
          ((Q a : DeletedCoeff p n) : Coeff p) m -
            ((D a : DeletedCoeff p n) : Coeff p) m := rfl
      _ = dualPairing (a : Coeff p) (k m) := by
        rw [hrow, show ((D a : DeletedCoeff p n) : Coeff p) m =
          d m * (a : Coeff p) m from deletedMultiplierCLM_apply n d a m]
        ring
  have hcompact : IsCompactOperator K :=
    isCompactOperator_deleted_of_reciprocalEntryBound hp n K b k
      hKrow hdiag hoff
  have hbij : Function.Bijective D := by
    exact (deletedMultiplierEquivOfLowerBound (p := p) n d c hc hlower).bijective
  refine ⟨D, K, hbij, hcompact, ?_, ?_⟩
  · dsimp [K]
    abel
  · intro m a
    exact deletedMultiplierCLM_apply n d a m

end NLS.Coeff
