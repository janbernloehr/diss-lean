import NLS.SequenceSpaces.RealPairedActionRotation

/-! # The group of paired action rotations -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞}

theorem actionRotation_pairedActionRotation_comm (z : RealCoeff p × RealCoeff p)
    (k l n : ℤ) (t u : ℝ) :
    actionRotation (pairedActionRotation z k l t) n u =
      pairedActionRotation (actionRotation z n u) k l t := by
  rw [pairedActionRotation,actionRotation_comm _ l n (-t) u,actionRotation_comm z k n t u]
  rfl

theorem pairedActionRotation_add (z : RealCoeff p × RealCoeff p) (k l : ℤ) (t u : ℝ) :
    pairedActionRotation (pairedActionRotation z k l t) k l u =
      pairedActionRotation z k l (t+u) := by
  unfold pairedActionRotation
  rw [actionRotation_comm (actionRotation z k t) l k (-t) u]
  simp only [actionRotation_add,neg_add]

theorem pairedActionRotation_comm (z : RealCoeff p × RealCoeff p) (k l m n : ℤ) (t u : ℝ) :
    pairedActionRotation (pairedActionRotation z k l t) m n u =
      pairedActionRotation (pairedActionRotation z m n u) k l t := by
  change actionRotation (actionRotation (pairedActionRotation z k l t) m u) n (-u) = _
  rw [actionRotation_pairedActionRotation_comm,actionRotation_pairedActionRotation_comm]
  rfl

theorem pairedActionRotation_periodic (z : RealCoeff p × RealCoeff p) (k l : ℤ) :
    Function.Periodic (pairedActionRotation z k l) (2*Real.pi) := by
  by_cases hkl : k = l
  · subst l
    intro t
    simp only [pairedActionRotation_same]
  intro t
  rw [pairedActionRotation_explicit z k l hkl,pairedActionRotation_explicit z k l hkl,
    Real.cos_add_two_pi,Real.sin_add_two_pi]

end NLS.RealCoeff
