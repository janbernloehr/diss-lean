import NLS.SequenceSpaces.RealActionReduction

/-! # Opening one zero Birkhoff mode

Adding a real amplitude in the first selected coordinate opens precisely
that mode. Its action is the square of the amplitude divided by two.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞}

def actionOpening (z : RealCoeff p × RealCoeff p) (n : ℤ) (t : ℝ) :
    RealCoeff p × RealCoeff p := z + t • (lp.single p n 1, 0)

@[simp] theorem actionOpening_zero (z : RealCoeff p × RealCoeff p) (n : ℤ) :
    actionOpening z n 0 = z := by simp [actionOpening]

theorem actionOpening_apply_same (z : RealCoeff p × RealCoeff p) (n : ℤ) (t : ℝ) :
    (actionOpening z n t).1 n = z.1 n+t ∧ (actionOpening z n t).2 n = z.2 n := by
  change z.1 n+t*(lp.single (E := fun _ : ℤ => ℝ) p n 1) n = z.1 n+t ∧ z.2 n+t*0 = z.2 n
  simp [lp.single_apply]

theorem actionOpening_apply_ne (z : RealCoeff p × RealCoeff p) (n k : ℤ)
    (hkn : k ≠ n) (t : ℝ) :
    (actionOpening z n t).1 k = z.1 k ∧ (actionOpening z n t).2 k = z.2 k := by
  change z.1 k+t*(lp.single (E := fun _ : ℤ => ℝ) p n 1) k = z.1 k ∧ z.2 k+t*0 = z.2 k
  simp [lp.single_apply,hkn]

theorem pairAction_actionOpening_same (z : RealCoeff p × RealCoeff p) (n : ℤ)
    (hz : z.1 n = 0 ∧ z.2 n = 0) (t : ℝ) :
    pairAction (actionOpening z n t) n = t^2/2 := by
  simp only [pairAction,(actionOpening_apply_same z n t).1,
    (actionOpening_apply_same z n t).2,hz.1,hz.2,zero_add,zero_pow (by norm_num : 2 ≠ 0),add_zero]

theorem pairAction_actionOpening_ne (z : RealCoeff p × RealCoeff p) (n k : ℤ)
    (hkn : k ≠ n) (t : ℝ) :
    pairAction (actionOpening z n t) k = pairAction z k := by
  rw [pairAction,(actionOpening_apply_ne z n k hkn t).1,(actionOpening_apply_ne z n k hkn t).2]
  rfl

/-- Action reduction along the opened ray is just a scalar change of amplitude. -/
theorem actionReduction_actionOpening (z : RealCoeff p × RealCoeff p) (n : ℤ)
    (hz : z.1 n = 0 ∧ z.2 n = 0) (t u : ℝ) :
    actionReduction (actionOpening z n t) n u =
      actionOpening z n (t*actionReductionScale (t^2/2) u) := by
  apply Prod.ext <;> ext k
  · by_cases hkn : k = n
    · subst k
      rw [(actionReduction_apply_same _ n u).1,(actionOpening_apply_same z n t).1,
        (actionOpening_apply_same z n _).1,pairAction_actionOpening_same z n hz,hz.1]
      ring
    · rw [(actionReduction_apply_ne _ n k hkn u).1,
        (actionOpening_apply_ne z n k hkn t).1,(actionOpening_apply_ne z n k hkn _).1]
  · by_cases hkn : k = n
    · subst k
      rw [(actionReduction_apply_same _ n u).2,(actionOpening_apply_same z n t).2,
        (actionOpening_apply_same z n _).2,hz.2,mul_zero]
    · rw [(actionReduction_apply_ne _ n k hkn u).2,
        (actionOpening_apply_ne z n k hkn t).2,(actionOpening_apply_ne z n k hkn _).2]

variable [Fact (1 ≤ p)]

theorem analyticOnNhd_actionOpening (z : RealCoeff p × RealCoeff p) (n : ℤ) :
    AnalyticOnNhd ℝ (actionOpening z n) univ := by
  intro t _
  exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)

theorem hasDerivAt_actionOpening (z : RealCoeff p × RealCoeff p) (n : ℤ) (t : ℝ) :
    HasDerivAt (actionOpening z n) (lp.single p n 1, 0) t := by
  simpa only [one_smul] using! ((hasDerivAt_id t).smul_const
    (lp.single p n 1, (0 : RealCoeff p))).const_add z

end NLS.RealCoeff
