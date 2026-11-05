import NLS.SequenceSpaces.ReflectionFixedActionCoordinates
import NLS.SequenceSpaces.RealActionHalfTurn

/-! # Only a central half turn can remain between fixed diagonal coordinates -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On a fixed action torus, positive coordinates determine a fixed point
up to a half turn of the central plane. -/
theorem eq_or_central_halfTurn_of_reflection_fixed (hp : p ≠ ⊤)
    (Q : (RealCoeff p × RealCoeff p) → (RealCoeff p × RealCoeff p)) (hQ : Continuous Q)
    (hrot : ∀ z k t, Q (actionRotation z k t) = actionRotation (Q z) (-k) (-t))
    (z w : RealCoeff p × RealCoeff p) (hz : Q z = z) (hw : Q w = w)
    (ha : ∀ n, pairAction z n = pairAction w n)
    (hpos : ∀ n : ℤ, 0 < n → z.1 n = w.1 n ∧ z.2 n = w.2 n) :
    w = z ∨ w = actionRotation z 0 Real.pi := by
  have hnonzero (n : ℤ) (hn : n ≠ 0) : z.1 n = w.1 n ∧ z.2 n = w.2 n := by
    by_cases hnp : 0 < n
    · exact hpos n hnp
    · have h := negative_coordinates_eq_of_reflection_fixed hp Q hQ hrot z w hz hw ha hpos n (by omega)
      exact ⟨h.1.symm,h.2.symm⟩
  obtain ⟨t,ht⟩ := exists_actionRotation_apply_eq z w 0 (ha 0)
  have he : actionRotation z 0 t = w := by
    apply Prod.ext <;> ext n
    · by_cases hn : n = 0
      · subst n; exact ht.1
      · exact (actionRotation_apply_ne z 0 n hn t).1.trans (hnonzero n hn).1
    · by_cases hn : n = 0
      · subst n; exact ht.2
      · exact (actionRotation_apply_ne z 0 n hn t).2.trans (hnonzero n hn).2
  have hsym := hrot z 0 t
  rw [he,hw,hz,neg_zero] at hsym
  have heq := he.trans hsym
  have hx := congrArg (fun v : RealCoeff p × RealCoeff p => v.1 0) heq
  have hy := congrArg (fun v : RealCoeff p × RealCoeff p => v.2 0) heq
  rw [(actionRotation_apply_same z 0 t).1,(actionRotation_apply_same z 0 (-t)).1] at hx
  rw [(actionRotation_apply_same z 0 t).2,(actionRotation_apply_same z 0 (-t)).2] at hy
  simp only [Real.cos_neg,Real.sin_neg] at hx hy
  by_cases hs : Real.sin t = 0
  · have hc : (Real.cos t)^2 = 1^2 := by nlinarith [Real.sin_sq_add_cos_sq t]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc with hc | hc
    · left
      rw [← he]
      apply Prod.ext <;> ext n
      · by_cases hn : n = 0
        · subst n; simp [(actionRotation_apply_same z 0 t).1,hs,hc]
        · exact (actionRotation_apply_ne z 0 n hn t).1
      · by_cases hn : n = 0
        · subst n; simp [(actionRotation_apply_same z 0 t).2,hs,hc]
        · exact (actionRotation_apply_ne z 0 n hn t).2
    · right
      rw [← he]
      apply Prod.ext <;> ext n
      · by_cases hn : n = 0
        · subst n; simp [(actionRotation_apply_same z 0 t).1,(actionRotation_pi_apply z 0 0).1,hs,hc]
        · rw [(actionRotation_apply_ne z 0 n hn t).1,(actionRotation_apply_ne z 0 n hn Real.pi).1]
      · by_cases hn : n = 0
        · subst n; simp [(actionRotation_apply_same z 0 t).2,(actionRotation_pi_apply z 0 0).2,hs,hc]
        · rw [(actionRotation_apply_ne z 0 n hn t).2,(actionRotation_apply_ne z 0 n hn Real.pi).2]
  · have hx0 : z.1 0 = 0 := (mul_eq_zero.mp (by linarith [hy] : Real.sin t*z.1 0 = 0)).resolve_left hs
    have hy0 : z.2 0 = 0 := (mul_eq_zero.mp (by linarith [hx] : Real.sin t*z.2 0 = 0)).resolve_left hs
    left
    rw [← he]
    apply actionRotation_eq_self_of_action_zero
    simp [pairAction,hx0,hy0]

end NLS.RealCoeff
