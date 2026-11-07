import NLS.SequenceSpaces.PhysicalRealMeanZeroWeightedExponent

/-! # Original physical weighted sequences constructed from literal raw data -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS

def physicalWeightedRawSequence (w : Weight) (p : ℝ≥0∞) [Fact (1≤p)]
    (a : ℤ → ℂ) (ha : Memℓp (fun j => (w j : ℂ)*a j) p)
    (hr : ∀ j : ℤ, a (-j)=(starRingEnd ℂ) (a j)) (hz : a 0=0) :
    physicalRealMeanZeroWeightedExponent w p := ⟨⟨a,ha⟩,hr,hz⟩

@[simp] theorem physicalWeightedRawSequence_apply (w : Weight) (p : ℝ≥0∞) [Fact (1≤p)]
    (a : ℤ → ℂ) (ha : Memℓp (fun j => (w j : ℂ)*a j) p)
    (hr : ∀ j : ℤ, a (-j)=(starRingEnd ℂ) (a j)) (hz : a 0=0) (j : ℤ) :
    (physicalWeightedRawSequence w p a ha hr hz).val.val j=a j := rfl

end NLS
