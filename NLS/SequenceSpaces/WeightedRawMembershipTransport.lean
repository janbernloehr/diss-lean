import NLS.SequenceSpaces.WeightedMultiplier

/-! # Transporting weighted membership along literal raw coefficient equality -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS

theorem weighted_memℓp_of_raw_eq (w : Weight) (p : ℝ≥0∞) (a b : ℤ → ℂ)
    (hb : Memℓp (fun n => (w n : ℂ)*b n) p) (he : ∀ n : ℤ, a n=b n) :
    Memℓp (fun n => (w n : ℂ)*a n) p := by
  have h : (fun n => (w n : ℂ)*a n)=(fun n => (w n : ℂ)*b n) :=
    funext (fun n => congrArg (fun z : ℂ => (w n : ℂ)*z) (he n))
  rw [h]
  exact hb

end NLS
