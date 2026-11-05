import NLS.SequenceSpaces.RealPairedActionRotation

/-! # Literal rectangular coordinates of the paired action group -/
noncomputable section
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞}

theorem pairedActionRotation_coordinates_of_ne_second (z : RealCoeff p × RealCoeff p)
    (k l m : ℤ) (hm : m ≠ l) (t : ℝ) :
    ((pairedActionRotation z k l t).1 m,(pairedActionRotation z k l t).2 m) =
      if m = k then (Real.cos t*z.1 m-Real.sin t*z.2 m,Real.sin t*z.1 m+Real.cos t*z.2 m)
      else (z.1 m,z.2 m) := by
  rw [pairedActionRotation,(actionRotation_apply_ne _ l m hm (-t)).1,
    (actionRotation_apply_ne _ l m hm (-t)).2]
  split_ifs with hmk
  · subst m
    exact Prod.ext (actionRotation_apply_same z k t).1 (actionRotation_apply_same z k t).2
  · exact Prod.ext (actionRotation_apply_ne z k m hmk t).1 (actionRotation_apply_ne z k m hmk t).2

end NLS.RealCoeff
