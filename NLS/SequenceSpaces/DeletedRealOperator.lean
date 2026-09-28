import NLS.SequenceSpaces.DeletedRealImag
import NLS.SequenceSpaces.DeletedJacobianMatrixExpansion

/-!
# Bounded deleted-coordinate operators with real matrix entries

At finite exponent, finite truncations determine a bounded operator on
the deleted sequence space. If all its matrix entries are real, it
commutes with pointwise conjugation and preserves the real and
imaginary components of every kernel direction.
-/

noncomputable section
open Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem deletedOperator_conj_apply_of_real_entries
    (hp : p ≠ ⊤) (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (hreal : ∀ m k : ℤ,
      (deletedOperatorMatrixEntry n Q m k).im = 0)
    (h : DeletedCoeff p n) (m : ℤ) :
    ((Q (DeletedCoeff.conj h) : DeletedCoeff p n) : Coeff p) m =
      star (((Q h : DeletedCoeff p n) : Coeff p) m) := by
  have hsum (s : Finset ℤ) :
      (∑ k ∈ s, ((DeletedCoeff.conj h : DeletedCoeff p n) : Coeff p) k *
        deletedOperatorMatrixEntry n Q m k) =
      star (∑ k ∈ s, (h : Coeff p) k *
        deletedOperatorMatrixEntry n Q m k) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [DeletedCoeff.conj_apply, star_mul]
    have hk : star (deletedOperatorMatrixEntry n Q m k) =
        deletedOperatorMatrixEntry n Q m k :=
      Complex.conj_eq_iff_im.mpr (hreal m k)
    rw [hk]
    ring
  have ht₁ := tendsto_deletedOperator_matrixSum hp n m Q
    (DeletedCoeff.conj h)
  have ht₂ := (continuous_star.tendsto
    (((Q h : DeletedCoeff p n) : Coeff p) m)).comp
      (tendsto_deletedOperator_matrixSum hp n m Q h)
  have ht₂' : Tendsto (fun s : Finset ℤ =>
      star (∑ k ∈ s, (h : Coeff p) k *
        deletedOperatorMatrixEntry n Q m k)) Filter.atTop
      (𝓝 (star (((Q h : DeletedCoeff p n) : Coeff p) m))) := by
    simpa only [Function.comp_def] using ht₂
  exact tendsto_nhds_unique ht₁ (ht₂'.congr' (Filter.Eventually.of_forall
    fun s => (hsum s).symm))

theorem deletedOperator_conj_of_real_entries
    (hp : p ≠ ⊤) (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (hreal : ∀ m k : ℤ,
      (deletedOperatorMatrixEntry n Q m k).im = 0)
    (h : DeletedCoeff p n) :
    Q (DeletedCoeff.conj h) = DeletedCoeff.conj (Q h) := by
  apply Subtype.ext
  ext m
  exact deletedOperator_conj_apply_of_real_entries hp n Q hreal h m

theorem deletedOperator_realPart_of_real_entries
    (hp : p ≠ ⊤) (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (hreal : ∀ m k : ℤ,
      (deletedOperatorMatrixEntry n Q m k).im = 0)
    (h : DeletedCoeff p n) :
    Q (DeletedCoeff.realPart h) = DeletedCoeff.realPart (Q h) := by
  simp only [DeletedCoeff.realPart, map_smul, map_add,
    deletedOperator_conj_of_real_entries hp n Q hreal h]

theorem deletedOperator_imagPart_of_real_entries
    (hp : p ≠ ⊤) (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (hreal : ∀ m k : ℤ,
      (deletedOperatorMatrixEntry n Q m k).im = 0)
    (h : DeletedCoeff p n) :
    Q (DeletedCoeff.imagPart h) = DeletedCoeff.imagPart (Q h) := by
  simp only [DeletedCoeff.imagPart, map_smul, map_sub,
    deletedOperator_conj_of_real_entries hp n Q hreal h]

theorem deletedOperator_kernel_realImag_of_real_entries
    (hp : p ≠ ⊤) (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (hreal : ∀ m k : ℤ,
      (deletedOperatorMatrixEntry n Q m k).im = 0)
    (h : DeletedCoeff p n) (hh : Q h = 0) :
    Q (DeletedCoeff.realPart h) = 0 ∧
      Q (DeletedCoeff.imagPart h) = 0 := by
  constructor
  · rw [deletedOperator_realPart_of_real_entries hp n Q hreal h,hh]
    simp [DeletedCoeff.realPart]
  · rw [deletedOperator_imagPart_of_real_entries hp n Q hreal h,hh]
    simp [DeletedCoeff.imagPart]

end NLS.Coeff
