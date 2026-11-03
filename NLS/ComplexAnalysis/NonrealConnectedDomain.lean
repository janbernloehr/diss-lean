import Mathlib.Analysis.Complex.Convex

/-! # Connected domains containing the nonreal plane and one real point -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

theorem isPreconnected_of_contains_nonreal {D : Set ℂ}
    (hD : ∀ z : ℂ, z.im ≠ 0 → z ∈ D) {x : ℂ} (hx : x ∈ D) (hxi : x.im = 0) :
    IsPreconnected D := by
  let A := D ∩ {z : ℂ | 0 ≤ z.im}
  let B := D ∩ {z : ℂ | z.im ≤ 0}
  have hA : IsConnected A := isConnected_of_upperHalfPlane (r := 0) (s := A)
    (fun z hz => ⟨hD z (ne_of_gt (show 0 < z.im from hz)),le_of_lt (show 0 < z.im from hz)⟩)
    inter_subset_right
  have hB : IsConnected B := isConnected_of_lowerHalfPlane (r := 0) (s := B)
    (fun z hz => ⟨hD z (ne_of_lt (show z.im < 0 from hz)),le_of_lt (show z.im < 0 from hz)⟩)
    inter_subset_right
  have he : D = A ∪ B := by
    ext z
    constructor
    · intro hz
      rcases le_total 0 z.im with h | h
      · exact Or.inl ⟨hz,h⟩
      · exact Or.inr ⟨hz,h⟩
    · rintro (h | h) <;> exact h.1
  rw [he]
  exact hA.isPreconnected.union x ⟨hx,hxi.ge⟩ ⟨hx,hxi.le⟩ hB.isPreconnected

end NLS.ComplexAnalysis
