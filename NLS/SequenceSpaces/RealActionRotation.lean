import NLS.SequenceSpaces.RealActionReduction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Complete one-mode action rotations

Rotate one real coordinate pair at unit angular speed. The construction
works at every sequence exponent and fixes every other coordinate. No
positive-action hypothesis is needed, so collapsed modes stay fixed.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞}

/-- The canonical action velocity in one coordinate plane. -/
def actionRotationVector (z : RealCoeff p × RealCoeff p) (k : ℤ) :
    RealCoeff p × RealCoeff p :=
  (-lp.single p k (z.2 k),lp.single p k (z.1 k))

/-- Rotate the selected pair, retaining every unselected coordinate. -/
def actionRotation (z : RealCoeff p × RealCoeff p) (k : ℤ) (t : ℝ) :
    RealCoeff p × RealCoeff p :=
  z+(Real.cos t-1) • pairMode z k+Real.sin t • actionRotationVector z k

@[simp] theorem actionRotation_zero (z : RealCoeff p × RealCoeff p) (k : ℤ) :
    actionRotation z k 0 = z := by
  simp [actionRotation]

theorem actionRotation_apply_same (z : RealCoeff p × RealCoeff p) (k : ℤ) (t : ℝ) :
    (actionRotation z k t).1 k = Real.cos t*z.1 k-Real.sin t*z.2 k ∧
    (actionRotation z k t).2 k = Real.sin t*z.1 k+Real.cos t*z.2 k := by
  change z.1 k+(Real.cos t-1)*(lp.single (E := fun _ : ℤ => ℝ) p k (z.1 k)) k+
      Real.sin t*(-(lp.single (E := fun _ : ℤ => ℝ) p k (z.2 k)) k) = _ ∧
    z.2 k+(Real.cos t-1)*(lp.single (E := fun _ : ℤ => ℝ) p k (z.2 k)) k+
      Real.sin t*(lp.single (E := fun _ : ℤ => ℝ) p k (z.1 k)) k = _
  simp only [lp.single_apply,Pi.single_eq_same]
  constructor <;> ring

theorem actionRotation_apply_ne (z : RealCoeff p × RealCoeff p) (k n : ℤ)
    (hn : n ≠ k) (t : ℝ) :
    (actionRotation z k t).1 n = z.1 n ∧ (actionRotation z k t).2 n = z.2 n := by
  change z.1 n+(Real.cos t-1)*(lp.single (E := fun _ : ℤ => ℝ) p k (z.1 k)) n+
      Real.sin t*(-(lp.single (E := fun _ : ℤ => ℝ) p k (z.2 k)) n) = _ ∧
    z.2 n+(Real.cos t-1)*(lp.single (E := fun _ : ℤ => ℝ) p k (z.2 k)) n+
      Real.sin t*(lp.single (E := fun _ : ℤ => ℝ) p k (z.1 k)) n = _
  simp [lp.single_apply,hn]

/-- All quadratic actions are preserved, including a collapsed selected mode. -/
theorem pairAction_actionRotation (z : RealCoeff p × RealCoeff p) (k n : ℤ) (t : ℝ) :
    pairAction (actionRotation z k t) n = pairAction z n := by
  by_cases hn : n = k
  · subst n
    rw [pairAction,(actionRotation_apply_same z k t).1,(actionRotation_apply_same z k t).2]
    dsimp [pairAction]
    nlinarith [Real.sin_sq_add_cos_sq t]
  · rw [pairAction,(actionRotation_apply_ne z k n hn t).1,(actionRotation_apply_ne z k n hn t).2]
    rfl

/-- A collapsed selected action gives the constant curve. -/
theorem actionRotation_eq_self_of_action_zero (z : RealCoeff p × RealCoeff p) (k : ℤ)
    (hk : pairAction z k = 0) (t : ℝ) : actionRotation z k t = z := by
  have hx : z.1 k = 0 := by
    have : (z.1 k)^2 = 0 := by dsimp [pairAction] at hk; nlinarith [sq_nonneg (z.2 k)]
    exact sq_eq_zero_iff.mp this
  have hy : z.2 k = 0 := by
    have : (z.2 k)^2 = 0 := by dsimp [pairAction] at hk; nlinarith [sq_nonneg (z.1 k)]
    exact sq_eq_zero_iff.mp this
  apply Prod.ext <;> ext n
  · by_cases hn : n = k
    · subst n
      simp [(actionRotation_apply_same z k t).1,hx,hy]
    · exact (actionRotation_apply_ne z k n hn t).1
  · by_cases hn : n = k
    · subst n
      simp [(actionRotation_apply_same z k t).2,hx,hy]
    · exact (actionRotation_apply_ne z k n hn t).2

/-- Rotation times add, so negative time supplies the inverse rotation. -/
theorem actionRotation_add (z : RealCoeff p × RealCoeff p) (k : ℤ) (t u : ℝ) :
    actionRotation (actionRotation z k t) k u = actionRotation z k (t+u) := by
  apply Prod.ext <;> ext n
  · by_cases hn : n = k
    · subst n
      rw [(actionRotation_apply_same _ k u).1,(actionRotation_apply_same z k t).1,
        (actionRotation_apply_same z k t).2,(actionRotation_apply_same z k (t+u)).1]
      rw [Real.cos_add,Real.sin_add]
      ring
    · rw [(actionRotation_apply_ne _ k n hn u).1,(actionRotation_apply_ne z k n hn t).1,
        (actionRotation_apply_ne z k n hn (t+u)).1]
  · by_cases hn : n = k
    · subst n
      rw [(actionRotation_apply_same _ k u).2,(actionRotation_apply_same z k t).1,
        (actionRotation_apply_same z k t).2,(actionRotation_apply_same z k (t+u)).2]
      rw [Real.cos_add,Real.sin_add]
      ring
    · rw [(actionRotation_apply_ne _ k n hn u).2,(actionRotation_apply_ne z k n hn t).2,
        (actionRotation_apply_ne z k n hn (t+u)).2]

variable [Fact (1 ≤ p)]

/-- The rotation solves its autonomous equation for all real times. -/
theorem hasDerivAt_actionRotation (z : RealCoeff p × RealCoeff p) (k : ℤ) (t : ℝ) :
    HasDerivAt (actionRotation z k) (actionRotationVector (actionRotation z k t) k) t := by
  have hd := (((Real.hasDerivAt_cos t).sub_const 1).smul_const (pairMode z k)).const_add z
  have h := hd.add ((Real.hasDerivAt_sin t).smul_const (actionRotationVector z k))
  have he : (-Real.sin t) • pairMode z k+Real.cos t • actionRotationVector z k =
      actionRotationVector (actionRotation z k t) k := by
    apply Prod.ext <;> ext n
    · change -Real.sin t*(lp.single (E := fun _ : ℤ => ℝ) p k (z.1 k)) n+
        Real.cos t*(-(lp.single (E := fun _ : ℤ => ℝ) p k (z.2 k)) n) =
        -(lp.single (E := fun _ : ℤ => ℝ) p k ((actionRotation z k t).2 k)) n
      rw [(actionRotation_apply_same z k t).2]
      by_cases hn : n = k
      · subst n
        simp only [lp.single_apply,Pi.single_eq_same]
        ring
      · simp [lp.single_apply,hn]
    · change -Real.sin t*(lp.single (E := fun _ : ℤ => ℝ) p k (z.2 k)) n+
        Real.cos t*(lp.single (E := fun _ : ℤ => ℝ) p k (z.1 k)) n =
        (lp.single (E := fun _ : ℤ => ℝ) p k ((actionRotation z k t).1 k)) n
      rw [(actionRotation_apply_same z k t).1]
      by_cases hn : n = k
      · subst n
        simp only [lp.single_apply,Pi.single_eq_same]
        ring
      · simp [lp.single_apply,hn]
  rw [he] at h
  exact h

end NLS.RealCoeff
