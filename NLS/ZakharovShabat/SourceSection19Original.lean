import NLS.ZakharovShabat.SourceSection19Laurent
import NLS.ZakharovShabat.SourceSection17Original

/-!
# Section 19 attached to the original Birkhoff family

Any existing original family retains its map and an open connected source
neighborhood inside its original domain. The entire real locus remains in
that neighborhood, with the original abelian integral assertions available
for one canonical primitive and one common domain.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Attach Section 19 to an already chosen original family. -/
theorem SourceSection17OriginalData.exists_section19
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (D : SourceSection17OriginalData hp hp1 W₀ W V s) :
    ∃ A U : Set (CoeffPair p), U ⊆ V ∧ SourceSection19Data hp hp1 A U :=
  exists_sourceSection19Data hp hp1 V D.complex.source_open D.complex.real_subset

/-- Unconditional original construction: no path integral, chart, mixed estimate,
or finite-gap physical realization is supplied as an assumption. -/
theorem sourceSection19_original (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      SourceSection17OriginalData hp hp1 W₀ W V s ∧
      ∃ A U : Set (CoeffPair p), U ⊆ V ∧ SourceSection19Data hp hp1 A U := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection17_original hp hp1
  exact ⟨W₀,W,V,s,D,D.exists_section19⟩

end NLS.ZakharovShabat
