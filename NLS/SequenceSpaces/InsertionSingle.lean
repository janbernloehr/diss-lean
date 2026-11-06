import NLS.SequenceSpaces.Insertion

noncomputable section
set_option autoImplicit false
open Classical
open scoped ENNReal

namespace NLS.Coeff



/-- Insertion preserves the original amplitude of each actual unit mode. -/
theorem insert_single {p : ℝ≥0∞} [Fact (1≤p)] (e : ℤ ↪ ℤ) (n : ℤ) (z : ℂ) :
    insert e (lp.single p n z)=lp.single p (e n) z := by
  ext m
  by_cases hm : m∈Set.range e
  · obtain ⟨j,rfl⟩ := hm
    rw [insert_apply_image]
    simp only [lp.single_apply,Pi.single_apply,e.injective.eq_iff]
  · rw [insert_apply_outside e _ m hm]
    have hmn : m≠e n := fun he => hm ⟨n,he.symm⟩
    simp only [lp.single_apply,Pi.single_apply,if_neg hmn]

end NLS.Coeff
