import NLS.ZakharovShabat.SourceSection20Frequencies
import NLS.ZakharovShabat.SourceSection20Factors

/-! # Unconditional original Section 20 construction

One original root family and one moment atlas support the full Section 20
package, on the same source domain as its Section 19 primitive.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceSection20_original (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ D : SourceSection17OriginalData hp hp1 W₀ W V s,
    ∃ Wa : Set (CoeffPair p), ∃ A : SourceAbelianMomentAtlas hp hp1 Wa s,
      ∃ B U : Set (CoeffPair p), SourceSection20Data D A B U := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection17_original hp hp1
  exact ⟨W₀,W,V,s,D,D.exists_section20⟩

end NLS.ZakharovShabat
