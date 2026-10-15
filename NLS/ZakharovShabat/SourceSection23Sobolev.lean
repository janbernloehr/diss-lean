import NLS.ZakharovShabat.SourceSection23Actions

/-! # Theorems 23.1–23.2 and Remark 23.3 for the original family

One common positive pair of constants controls all four estimates, before
choosing the potential. The action norms use the original indexed actions.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Simultaneous Birkhoff and action estimates with the same constants. -/
structure SourceSection23SobolevBounds {W₀ B W : Set (CoeffPair 2)}
    {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}
    (D : SourceSection17OriginalData (by simp) (by norm_num) W₀ B W s)
    (m : ℕ) (hm : 1 ≤ m) (c d : ℝ) : Prop where
  c_pos : 0 < c
  d_pos : 0 < d
  action_summable : ∀ a : realTypeHigherSobolevSourceLocus m,
    Summable (sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m)
  birkhoff_upper : ∀ a : realTypeHigherSobolevSourceLocus m,
    ‖D.complex.sobolevCoordinates m hm m le_rfl a‖ ≤ c*
      (‖sourcePiSobolevCoordinates m m le_rfl a.val‖+
        (1+‖sourcePiSobolevCoordinates m 1 hm a.val‖)^(2*m)*‖higherSobolevSourceInclusion m a.val‖)
  birkhoff_lower : ∀ a : realTypeHigherSobolevSourceLocus m,
    ‖sourcePiSobolevCoordinates m m le_rfl a.val‖ ≤ d*
      (‖D.complex.sobolevCoordinates m hm m le_rfl a‖+
        (1+‖D.complex.sobolevCoordinates m hm 1 hm a‖)^(4*m-3)*‖D.complex.sobolevCoordinates m hm 0 (Nat.zero_le m) a‖)
  action_upper : ∀ a : realTypeHigherSobolevSourceLocus m,
    (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n) ≤
      c^2*(‖sourcePiSobolevCoordinates m m le_rfl a.val‖^2+
        (1+‖sourcePiSobolevCoordinates m 1 hm a.val‖)^(4*m)*‖higherSobolevSourceInclusion m a.val‖^2)
  action_lower : ∀ a : realTypeHigherSobolevSourceLocus m,
    ‖sourcePiSobolevCoordinates m m le_rfl a.val‖^2 ≤ d^2*
      ((∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
        (1+∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
          (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n))

namespace SourceSection17OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The same original Birkhoff map has common positive constants in both theorems. -/
theorem section23_sobolev_bounds
    (D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s)
    (m : ℕ) (hm : 1 ≤ m) : ∃ c d : ℝ, SourceSection23SobolevBounds D m hm c d := by
  obtain ⟨c,d,H⟩ := D.complex.exists_sobolev_joint_bounds m hm
  refine ⟨c,d,H.c_pos,H.d_pos,?_,H.birkhoff_upper,H.birkhoff_lower,?_,?_⟩
  · intro a
    exact (H.action_summable a).congr (fun n =>
      (sourceIndexedWeightedActionTerm_eq
        ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n).symm)
  · simpa only [sourceIndexedWeightedActionTerm_eq] using H.action_upper
  · simpa only [sourceIndexedWeightedActionTerm_eq] using H.action_lower
end SourceSection17OriginalData
end NLS.ZakharovShabat
