import NLS.SequenceSpaces.RealActionRotation

/-! # Exact half turns of a real action plane -/
noncomputable section
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞}

theorem actionRotation_pi_apply (z : RealCoeff p × RealCoeff p) (k n : ℤ) :
    (actionRotation z k Real.pi).1 n = (if n = k then -z.1 n else z.1 n) ∧
      (actionRotation z k Real.pi).2 n = (if n = k then -z.2 n else z.2 n) := by
  by_cases hn : n = k
  · subst n
    simp [(actionRotation_apply_same z k Real.pi).1,(actionRotation_apply_same z k Real.pi).2]
  · simpa only [if_neg hn] using actionRotation_apply_ne z k n hn Real.pi

theorem actionRotation_pi_eq_neg_pi (z : RealCoeff p × RealCoeff p) (k : ℤ) :
    actionRotation z k Real.pi = actionRotation z k (-Real.pi) := by
  apply Prod.ext <;> ext n
  · by_cases hn : n = k
    · subst n
      simp [(actionRotation_apply_same z k Real.pi).1,(actionRotation_apply_same z k (-Real.pi)).1]
    · rw [(actionRotation_apply_ne z k n hn Real.pi).1,(actionRotation_apply_ne z k n hn (-Real.pi)).1]
  · by_cases hn : n = k
    · subst n
      simp [(actionRotation_apply_same z k Real.pi).2,(actionRotation_apply_same z k (-Real.pi)).2]
    · rw [(actionRotation_apply_ne z k n hn Real.pi).2,(actionRotation_apply_ne z k n hn (-Real.pi)).2]

theorem actionRotation_pi_eq_self_iff (z : RealCoeff p × RealCoeff p) (k : ℤ) :
    actionRotation z k Real.pi = z ↔ pairAction z k = 0 := by
  constructor
  · intro he
    have hx := congrArg (fun v : RealCoeff p × RealCoeff p => v.1 k) he
    have hy := congrArg (fun v : RealCoeff p × RealCoeff p => v.2 k) he
    rw [(actionRotation_pi_apply z k k).1,if_pos rfl] at hx
    rw [(actionRotation_pi_apply z k k).2,if_pos rfl] at hy
    have hx0 : z.1 k = 0 := by linarith
    have hy0 : z.2 k = 0 := by linarith
    simp [pairAction,hx0,hy0]
  · intro he
    exact actionRotation_eq_self_of_action_zero z k he Real.pi

end NLS.RealCoeff
