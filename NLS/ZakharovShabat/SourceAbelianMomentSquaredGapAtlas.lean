import NLS.ZakharovShabat.SourceAbelianMomentAtlas
import NLS.ZakharovShabat.SourcePsiLemma12_12

/-! # Actual moment atlases retaining squared-gap psi estimates

The same chosen psi branch carries both the normalized moment atlas and
the squared-gap extension. Thus the inputs of Lemma 20.3 and Theorem 20.4
are constructed together, rather than assumed independently compatible.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At every finite p > 1, construct an actual moment atlas using the
very same branch as the squared-gap complex psi extension. -/
theorem exists_sourceAbelianMoment_squaredGapAtlas (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      IsOpen V ∧ realTypeSourceLocus p ⊆ V ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 V s ∧
          Nonempty (SourceAbelianMomentAtlas hp hp1 W s) := by
  classical
  obtain ⟨_,V,_,hV,_,hrealV,_,s,hs⟩ := exists_sourcePsi_lemma12_12 hp hp1
  obtain ⟨W,hW,hrealW,hlocal⟩ := hs.toSourcePsiNormalizedComplexExtension.exists_moment_localCharts hV hrealV
  choose L hL using hlocal
  exact ⟨W,V,hW,hrealW,hV,hrealV,s,hs,⟨⟨L⟩⟩⟩

end NLS.ZakharovShabat
