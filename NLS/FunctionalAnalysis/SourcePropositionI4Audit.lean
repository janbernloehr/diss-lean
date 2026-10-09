import NLS.FunctionalAnalysis.SourceSchurComplement

/-! # The Schur signs in the proof of Proposition I.4

The displayed finite block on page 140 has the opposite signs from the
Schur complement in I.1. The printed block can have nonzero determinant
while the full operator is singular. This audits the proof formula, not
the generic local invertibility assertion of Proposition I.4.
-/
noncomputable section
namespace NLS.SchurComplement

/-- The finite block printed in the proof of I.4. -/
def sourceI4PrintedSchur (A B C D : ℂ →L[ℂ] ℂ) : ℂ →L[ℂ] ℂ :=
  1-A+B.comp ((Ring.inverse (1+D)).comp C)

/-- For A=D=0 and B=C=Id the printed determinant gives a false positive:
the printed block is twice the identity but the full matrix has two equal rows. -/
theorem sourceI4_printedSchur_false_positive :
    (sourceI4PrintedSchur 0 1 1 0).toLinearMap.det ≠ 0 ∧
    ¬IsUnit (1+block (0 : ℂ →L[ℂ] ℂ) 1 1 (0 : ℂ →L[ℂ] ℂ)) := by
  constructor
  · have he : sourceI4PrintedSchur 0 1 1 0 = (2 : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
      ext; norm_num [sourceI4PrintedSchur]
    rw [he]
    simp
  · rw [sourceCorollaryI2_iff _ _ _ _ (by simp)]
    simp [sourceSchur,expression]

/-- The corrected Schur block detects this singular operator exactly. -/
theorem sourceI4_correctSchur_zero :
    sourceSchur (0 : ℂ →L[ℂ] ℂ) 1 1 (0 : ℂ →L[ℂ] ℂ) = 0 := by
  ext; simp [sourceSchur,expression]

end NLS.SchurComplement
