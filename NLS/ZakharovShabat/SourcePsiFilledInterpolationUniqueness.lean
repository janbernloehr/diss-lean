import NLS.ZakharovShabat.SourcePsiDeletedRootFill
import NLS.ZakharovShabat.SourcePsiInterpolationQuotientExterior

/-!
# Gap interpolation with a freely filled deleted root

The psi numerator uses only retained roots. Its missing root can be
placed in the assigned isolating disc for the interpolation product,
even when the deleted-sequence representation has zero displacement
at that index.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Gap zeros force a deleted direction to vanish when retained roots
are localized and one arbitrary fill point lies in the deleted disc. -/
theorem sourcePsiCandidate_deleted_direction_zero_of_gapZeros_with_fill
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (n : ℤ) (a h : DeletedCoeff p n) (ξ : ℂ)
    (hseg : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆
        sourceIsolatingDisc hp hp1 φ N ε m)
    (hrootloc : ∀ m : ℤ, m ≠ n →
      displacedRoots (a : Coeff p) m ∈
        sourceIsolatingDisc hp hp1 φ N ε m)
    (hξ : ξ ∈ sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (hgap : ∀ m : ℤ, m ≠ n →
      ∃ μ ∈ sourcePeriodicSegment hp hp1 ψ m,
        sourcePsiCandidateVariation n (a : Coeff p) (h : Coeff p) μ = 0) :
    h = 0 := by
  let aFull : Coeff p := sourcePsiFillDeletedRoot n a ξ
  have hroots : ∀ m : ℤ,
      displacedRoots aFull m ∈ sourceIsolatingDisc hp hp1 φ N ε m := by
    intro m
    by_cases hmn : m = n
    · subst m
      simpa only [aFull, displacedRoots_sourcePsiFillDeletedRoot_same] using hξ
    · rw [show displacedRoots aFull m =
          displacedRoots (a : Coeff p) m from
            displacedRoots_sourcePsiFillDeletedRoot_other n m hmn a ξ]
      exact hrootloc m hmn
  have hsep : Function.Injective (displacedRoots aFull) :=
    displacedRoots_injective_of_isolatingDiscs
      hp hp1 φ N ε aFull hroots hdisjoint
  have hzero : (h : Coeff p) = 0 := by
    apply sourcePsiCandidate_deleted_direction_zero_of_gapZeros
      hp hp1 φ ψ N ε n aFull (h : Coeff p)
        hsep h.property hseg (hroots n) hdisjoint
    intro m hmn
    obtain ⟨μ,hμ,hμzero⟩ := hgap m hmn
    refine ⟨μ,hμ,?_⟩
    rw [sourcePsiCandidateVariation_fillDeletedRoot hp hp1 n a
      (h : Coeff p) ξ μ]
    exact hμzero
  exact Subtype.ext hzero

end NLS.ZakharovShabat
