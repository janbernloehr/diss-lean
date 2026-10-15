import NLS.SequenceSpaces.DeletedRealOperator

/-!
# Reality of inverse deleted-coordinate operators

A bounded operator with real matrix entries preserves real inputs.
When it is an equivalence, its inverse commutes with conjugation and
also preserves real inputs.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem deletedEquiv_symm_conj_of_real_entries
    (hp : p ≠ ⊤) (n : ℤ) (e : DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n)
    (hr : ∀ m k : ℤ, (deletedOperatorMatrixEntry n e.toContinuousLinearMap m k).im = 0)
    (h : DeletedCoeff p n) : e.symm (DeletedCoeff.conj h) = DeletedCoeff.conj (e.symm h) := by
  apply e.injective
  rw [e.apply_symm_apply]
  change DeletedCoeff.conj h = e.toContinuousLinearMap (DeletedCoeff.conj (e.symm h))
  rw [deletedOperator_conj_of_real_entries hp n e.toContinuousLinearMap hr]
  simp

theorem deletedEquiv_symm_real_of_real_entries
    (hp : p ≠ ⊤) (n : ℤ) (e : DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n)
    (hr : ∀ m k : ℤ, (deletedOperatorMatrixEntry n e.toContinuousLinearMap m k).im = 0)
    (h : DeletedCoeff p n) (hh : ∀ m : ℤ, ((h:Coeff p) m).im = 0) :
    ∀ m : ℤ, ((e.symm h:Coeff p) m).im = 0 := by
  have hconj : DeletedCoeff.conj h = h := by
    apply Subtype.ext
    ext m
    exact Complex.conj_eq_iff_im.mpr (hh m)
  have he := deletedEquiv_symm_conj_of_real_entries hp n e hr h
  rw [hconj] at he
  intro m
  apply Complex.conj_eq_iff_im.mp
  exact (congrArg (fun b : DeletedCoeff p n => (b:Coeff p) m) he).symm

theorem deletedOperator_real_of_real_entries
    (hp : p ≠ ⊤) (n : ℤ) (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (hr : ∀ m k : ℤ, (deletedOperatorMatrixEntry n Q m k).im = 0)
    (h : DeletedCoeff p n) (hh : ∀ m : ℤ, ((h:Coeff p) m).im = 0) :
    ∀ m : ℤ, ((Q h:Coeff p) m).im = 0 := by
  have hconj : DeletedCoeff.conj h = h := by
    apply Subtype.ext
    ext m
    exact Complex.conj_eq_iff_im.mpr (hh m)
  have he := deletedOperator_conj_of_real_entries hp n Q hr h
  rw [hconj] at he
  intro m
  apply Complex.conj_eq_iff_im.mp
  exact (congrArg (fun b : DeletedCoeff p n => (b:Coeff p) m) he).symm

end NLS.Coeff
