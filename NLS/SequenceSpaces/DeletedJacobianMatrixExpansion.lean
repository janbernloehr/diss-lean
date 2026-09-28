import NLS.SequenceSpaces.DeletedJacobianSymbol
import NLS.SequenceSpaces.Truncation

/-!
# Matrix expansion on deleted-coordinate truncations

A bounded operator on deleted `ℓᵖ` is determined by its matrix entries
on retained coordinate vectors. Finite input truncations give the
corresponding finite matrix sum, and converge in the deleted space at
every finite Banach exponent.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A matrix entry that also makes sense at the deleted input index,
where the projected coordinate vector is zero. -/
def deletedOperatorMatrixEntry (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (m k : ℤ) : ℂ :=
  ((Q (deleteCoordinateTo n (lp.single p k 1)) :
    DeletedCoeff p n) : Coeff p) m

theorem deletedOperatorMatrixEntry_apply_other (n m k : ℤ)
    (hkn : k ≠ n)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    deletedOperatorMatrixEntry n Q m k =
      ((Q (deletedSingleCLM n k hkn 1) : DeletedCoeff p n) : Coeff p) m := by
  simp [deletedOperatorMatrixEntry,deleteCoordinateTo_single_other n k hkn]

@[simp] theorem deletedOperatorMatrixEntry_apply_deleted (n m : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    deletedOperatorMatrixEntry n Q m n = 0 := by
  simp [deletedOperatorMatrixEntry,deleteCoordinateTo_single_same]

/-- On a finite input truncation, a bounded deleted-coordinate
operator is exactly the finite sum of its matrix entries. -/
theorem deletedOperator_truncate_matrixExpansion (n m : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (a : DeletedCoeff p n) (s : Finset ℤ) :
    ((Q (deleteCoordinateTo n (truncate s (a : Coeff p))) :
      DeletedCoeff p n) : Coeff p) m =
      ∑ k ∈ s, (a : Coeff p) k * deletedOperatorMatrixEntry n Q m k := by
  let e : ℤ → DeletedCoeff p n := fun k =>
    deleteCoordinateTo n (lp.single p k 1)
  have hsingle (k : ℤ) :
      (lp.single p k ((a : Coeff p) k) : Coeff p) =
        (a : Coeff p) k • (lp.single p k (1 : ℂ) : Coeff p) := by
    ext r
    by_cases hrk : r = k
    · subst r
      simp
    · simp [hrk]
  have htrunc : deleteCoordinateTo n (truncate s (a : Coeff p)) =
      ∑ k ∈ s, (a : Coeff p) k • e k := by
    rw [truncate]
    simp_rw [hsingle]
    simp [e, map_sum, map_smul]
  let L : DeletedCoeff p n →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL)
  change (L.comp Q) (deleteCoordinateTo n (truncate s (a : Coeff p))) =
    ∑ k ∈ s, (a : Coeff p) k * (L.comp Q) (e k)
  rw [htrunc, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul]
  rfl

/-- Projected finite truncations converge to the deleted-coordinate
input when the exponent is finite. -/
theorem tendsto_deleted_truncate (hp : p ≠ ⊤) (n : ℤ)
    (a : DeletedCoeff p n) :
    Tendsto
      (fun s : Finset ℤ => deleteCoordinateTo n
        (truncate s (a : Coeff p))) atTop (𝓝 a) := by
  have hproj : deleteCoordinateTo n (a : Coeff p) = a := by
    apply Subtype.ext
    exact (deleteCoordinate_eq_self_iff n (a : Coeff p)).2 a.property
  have ht := ((deleteCoordinateTo (p := p) n).continuous.tendsto
    (a : Coeff p)).comp (tendsto_truncate hp (a : Coeff p))
  simpa only [Function.comp_def,hproj] using ht

/-- The finite matrix sums of a bounded deleted-coordinate operator
converge to each output coordinate. -/
theorem tendsto_deletedOperator_matrixSum (hp : p ≠ ⊤)
    (n m : ℤ) (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (a : DeletedCoeff p n) :
    Tendsto (fun s : Finset ℤ =>
      ∑ k ∈ s, (a : Coeff p) k * deletedOperatorMatrixEntry n Q m k)
      atTop (𝓝 (((Q a : DeletedCoeff p n) : Coeff p) m)) := by
  let L : DeletedCoeff p n →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL)
  have ht := ((L.comp Q).continuous.tendsto a).comp
    (tendsto_deleted_truncate hp n a)
  change Tendsto (fun s : Finset ℤ =>
    ∑ k ∈ s, (a : Coeff p) k * deletedOperatorMatrixEntry n Q m k)
      atTop (𝓝 ((L.comp Q) a))
  have hsum (s : Finset ℤ) :
      (L.comp Q) (deleteCoordinateTo n (truncate s (a : Coeff p))) =
        ∑ k ∈ s, (a : Coeff p) k * deletedOperatorMatrixEntry n Q m k :=
    deletedOperator_truncate_matrixExpansion n m Q a s
  simpa only [Function.comp_def,hsum] using ht

end NLS.Coeff
