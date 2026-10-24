import NLS.FunctionalAnalysis.PeriodicGridCover
import NLS.FunctionalAnalysis.CircleProductCoveringDimensionLower
import NLS.FunctionalAnalysis.CoveringDimensionValue

/-! # Exact covering dimension of a finite product of circles

Periodic grid refinements prove the upper bound. Closed cubes in distinct
circle factors prove the matching lower bound. Both use the same standard
finite-open-refinement definition of covering dimension.
-/
noncomputable section
set_option autoImplicit false
namespace NLS.FunctionalAnalysis
universe u
section Finite
variable {ι : Type u} [Fintype ι]

/-- The standard covering-dimension upper bound for a finite torus. -/
theorem hasCoveringDimensionLE_circleProduct :
    HasCoveringDimensionLE (ι → Circle) (Fintype.card ι) :=
  hasCoveringDimensionLE_addCircleProduct.homeomorph
    (Homeomorph.piCongrRight (fun _ : ι => AddCircle.homeomorphCircle one_ne_zero))

/-- A natural number bounds the dimension of a finite torus exactly when it bounds its factor count. -/
theorem hasCoveringDimensionLE_circleProduct_iff (n : ℕ) :
    HasCoveringDimensionLE (ι → Circle) n ↔ Fintype.card ι ≤ n :=
  ⟨card_le_of_hasCoveringDimensionLE_circleProduct,
    fun h => hasCoveringDimensionLE_circleProduct.mono h⟩

/-- The numerical covering dimension of a finite torus is exactly its number of factors. -/
theorem coveringDimension_circleProduct :
    coveringDimension (ι → Circle) = (Fintype.card ι : WithBot ℕ∞) := by
  classical
  have hn : ¬ IsEmpty (ι → Circle) := not_isEmpty_of_nonempty _
  have hb : ∃ n, HasCoveringDimensionLE (ι → Circle) n :=
    ⟨Fintype.card ι,hasCoveringDimensionLE_circleProduct⟩
  have hf : Nat.find hb = Fintype.card ι := le_antisymm
    (Nat.find_min' hb hasCoveringDimensionLE_circleProduct)
    (card_le_of_hasCoveringDimensionLE_circleProduct (Nat.find_spec hb))
  simp only [coveringDimension,if_neg hn,dif_pos hb,hf]

end Finite

/-- Finite and infinite circle products have dimension equal to their extended factor count. -/
theorem coveringDimension_circleProduct_eq_card (ι : Type u) :
    coveringDimension (ι → Circle) = (ENat.card ι : WithBot ℕ∞) := by
  classical
  cases finite_or_infinite ι with
  | inl hf =>
    let := hf
    let := Fintype.ofFinite ι
    simpa using coveringDimension_circleProduct (ι := ι)
  | inr hi =>
    let := hi
    rw [ENat.card_eq_top_of_infinite]
    apply coveringDimension_eq_top_iff.mpr
    intro n
    exact not_hasCoveringDimensionLE_circleProduct_of_embedding
      ((⟨Fin.val,Fin.val_injective⟩ : Fin (n+1) ↪ ℕ).trans (Infinite.natEmbedding ι))

end NLS.FunctionalAnalysis
