import NLS.ZakharovShabat.SourceBirkhoffInjectivityReduction
import NLS.ZakharovShabat.SourceHilbertGlobalInverse

/-! # Proposition 17.2: global injectivity at every finite exponent above one

The constructed Hilbert global inverse discharges the last premise in the
exponent-extension argument. Together with Proposition 17.1, this also
makes every actual real Birkhoff map an open embedding.
-/
noncomputable section
open Set Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Proposition 17.2: the real Birkhoff map is one-to-one for `1 < p < ∞`. -/
theorem proposition17_2 (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    Function.Injective (sourceRealBirkhoffMap hp hp1 s) := by
  obtain ⟨V₀,C,V,t,E⟩ :=
    exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  exact D.real_map_injective_of_hilbert E E.hilbert_real_map_bijective.1

/-- The actual real map identifies its source with an open subset of the target. -/
theorem real_map_isOpenEmbedding (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    IsOpenEmbedding (sourceRealBirkhoffMap hp hp1 s) :=
  D.real_map_isLocalHomeomorph.isOpenEmbedding_of_injective D.proposition17_2

end SourceBirkhoffMapComplexData

/-- A normalized family with globally injective real Birkhoff map is constructed
at every finite exponent above one. -/
theorem exists_sourceBirkhoffFamily_injective (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
      SourceBirkhoffMapComplexData hp hp1 W₀ B W s ∧
      Function.Injective (sourceRealBirkhoffMap hp hp1 s) := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨W₀,B,W,s,D,D.proposition17_2⟩

end NLS.ZakharovShabat
