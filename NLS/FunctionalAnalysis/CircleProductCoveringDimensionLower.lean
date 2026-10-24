import NLS.FunctionalAnalysis.CircleProductCubeEmbedding
import NLS.FunctionalAnalysis.CubeCoveringDimensionLower

/-! # Covering-dimension lower bounds from distinct circle factors

The short-arc closed embeddings and the numerical cube lower bound count
any finite collection of distinct circle factors. No finite-dimensional
upper bound is asserted here.
-/
noncomputable section
set_option autoImplicit false
open scoped unitInterval
namespace NLS.FunctionalAnalysis
universe u
variable {ι : Type u}

/-- n+1 distinct circle factors exclude a covering-dimension bound n. -/
theorem not_hasCoveringDimensionLE_circleProduct_of_embedding {n : ℕ}
    (e : Fin (n+1) ↪ ι) : ¬ HasCoveringDimensionLE (ι → Circle) n := by
  intro h
  exact not_hasCoveringDimensionLE_cube n
    (h.of_isClosedEmbedding (isClosedEmbedding_circleProductCubeMap e))

/-- Every covering-dimension bound on a finite circle product bounds its factor count. -/
theorem card_le_of_hasCoveringDimensionLE_circleProduct [Fintype ι] {n : ℕ}
    (h : HasCoveringDimensionLE (ι → Circle) n) : Fintype.card ι ≤ n := by
  by_contra hn
  have hle : n+1 ≤ Fintype.card ι := by omega
  let e : Fin (n+1) ↪ ι := (Fin.castLEEmb hle).trans (Fintype.equivFin ι).symm.toEmbedding
  exact not_hasCoveringDimensionLE_circleProduct_of_embedding e h

end NLS.FunctionalAnalysis
