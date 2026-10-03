import Mathlib.Analysis.Calculus.Deriv.Add
import NLS.SequenceSpaces.RealCoeff
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # The one-mode action-reduction curve

Rescaling one real coordinate pair reduces its quadratic action at unit
speed. The curve is continuous through the collapsed endpoint and smooth
on the entire interval before it. It is defined in every real sequence
space, so this coordinate construction is independent of the exponent.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞}

/-- The quadratic action of a real coordinate pair. -/
def pairAction (z : RealCoeff p × RealCoeff p) (k : ℤ) : ℝ :=
  ((z.1 k)^2+(z.2 k)^2)/2

/-- The selected coordinate pair, embedded with support at one index. -/
def pairMode (z : RealCoeff p × RealCoeff p) (k : ℤ) : RealCoeff p × RealCoeff p :=
  (lp.single p k (z.1 k),lp.single p k (z.2 k))

/-- The radial factor reducing an initially positive action `a` by `t`. -/
def actionReductionScale (a t : ℝ) : ℝ := Real.sqrt (1-t/a)

/-- Reduce a single action while retaining its direction and all other modes. -/
def actionReduction (z : RealCoeff p × RealCoeff p) (k : ℤ) (t : ℝ) :
    RealCoeff p × RealCoeff p :=
  z+(actionReductionScale (pairAction z k) t-1) • pairMode z k

@[simp] theorem actionReduction_zero (z : RealCoeff p × RealCoeff p) (k : ℤ) :
    actionReduction z k 0 = z := by
  simp [actionReduction,actionReductionScale]

theorem actionReduction_apply_same (z : RealCoeff p × RealCoeff p) (k : ℤ) (t : ℝ) :
    (actionReduction z k t).1 k = actionReductionScale (pairAction z k) t*z.1 k ∧
    (actionReduction z k t).2 k = actionReductionScale (pairAction z k) t*z.2 k := by
  change z.1 k+(actionReductionScale (pairAction z k) t-1)*(lp.single (E := fun _ : ℤ => ℝ) p k (z.1 k)) k = _ ∧
    z.2 k+(actionReductionScale (pairAction z k) t-1)*(lp.single (E := fun _ : ℤ => ℝ) p k (z.2 k)) k = _
  simp only [lp.single_apply,Pi.single_eq_same]
  constructor <;> ring

theorem actionReduction_apply_ne (z : RealCoeff p × RealCoeff p) (k n : ℤ)
    (hn : n ≠ k) (t : ℝ) :
    (actionReduction z k t).1 n = z.1 n ∧ (actionReduction z k t).2 n = z.2 n := by
  change z.1 n+(actionReductionScale (pairAction z k) t-1)*(lp.single (E := fun _ : ℤ => ℝ) p k (z.1 k)) n = _ ∧
    z.2 n+(actionReductionScale (pairAction z k) t-1)*(lp.single (E := fun _ : ℤ => ℝ) p k (z.2 k)) n = _
  simp [lp.single_apply,hn]

/-- Exact unit-speed reduction, including the collapsed endpoint. -/
theorem pairAction_actionReduction_same (z : RealCoeff p × RealCoeff p) (k : ℤ)
    (ha : 0 < pairAction z k) (t : ℝ) (ht : t ≤ pairAction z k) :
    pairAction (actionReduction z k t) k = pairAction z k-t := by
  have hpos : 0 ≤ 1-t/pairAction z k := by
    have := (div_le_one ha).mpr ht
    linarith
  have hsq := Real.sq_sqrt hpos
  rw [pairAction,(actionReduction_apply_same z k t).1,(actionReduction_apply_same z k t).2]
  dsimp only [actionReductionScale]
  rw [mul_pow,mul_pow]
  rw [hsq]
  have hne := ne_of_gt ha
  calc
    _ = (1-t/pairAction z k)*pairAction z k := by dsimp [pairAction]; ring
    _ = pairAction z k-t := by field_simp

/-- Every unselected action is conserved. -/
theorem pairAction_actionReduction_ne (z : RealCoeff p × RealCoeff p) (k n : ℤ)
    (hn : n ≠ k) (t : ℝ) :
    pairAction (actionReduction z k t) n = pairAction z n := by
  simp only [pairAction,(actionReduction_apply_ne z k n hn t).1,
    (actionReduction_apply_ne z k n hn t).2]

variable [Fact (1 ≤ p)]

theorem continuous_actionReduction (z : RealCoeff p × RealCoeff p) (k : ℤ) :
    Continuous (actionReduction z k) := by
  exact continuous_const.add
    (((Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.div_const _))).sub
      continuous_const).smul continuous_const)

/-- Smoothness holds before the selected action reaches zero. -/
theorem contDiffAt_actionReduction (z : RealCoeff p × RealCoeff p) (k : ℤ)
    (ha : 0 < pairAction z k) {t : ℝ} (ht : t < pairAction z k) :
    ContDiffAt ℝ ⊤ (actionReduction z k) t := by
  have hpos : 0 < 1-t/pairAction z k := by
    have := (div_lt_one ha).mpr ht
    linarith
  exact contDiffAt_const.add
    ((((contDiffAt_const.sub (contDiffAt_id.div_const _)).sqrt (ne_of_gt hpos)).sub
      contDiffAt_const).smul contDiffAt_const)

/-- The exact coordinate velocity; the negative sign occurs in both components. -/
theorem hasDerivAt_actionReduction (z : RealCoeff p × RealCoeff p) (k : ℤ)
    (ha : 0 < pairAction z k) {t : ℝ} (ht : t < pairAction z k) :
    HasDerivAt (actionReduction z k)
      ((-(1 / pairAction z k) / (2*actionReductionScale (pairAction z k) t)) • pairMode z k) t := by
  have hpos : 0 < 1-t/pairAction z k := by
    have := (div_lt_one ha).mpr ht
    linarith
  have hd := HasDerivAt.sqrt (((hasDerivAt_id t).div_const (pairAction z k)).const_sub 1) (ne_of_gt hpos)
  convert! ((hd.sub_const 1).smul_const (pairMode z k)).const_add z using 1

/-- The radial vector field lowering the selected action at unit speed. -/
def actionReductionVector (z : RealCoeff p × RealCoeff p) (k : ℤ) :
    RealCoeff p × RealCoeff p :=
  (-(1 / (2*pairAction z k))) • pairMode z k

omit [Fact (1 ≤ p)] in
/-- The selected-mode projection scales by the same radial factor. -/
theorem pairMode_actionReduction (z : RealCoeff p × RealCoeff p) (k : ℤ) (t : ℝ) :
    pairMode (actionReduction z k t) k =
      actionReductionScale (pairAction z k) t • pairMode z k := by
  apply Prod.ext <;> ext n
  · change (lp.single (E := fun _ : ℤ => ℝ) p k ((actionReduction z k t).1 k)) n =
      actionReductionScale (pairAction z k) t*(lp.single (E := fun _ : ℤ => ℝ) p k (z.1 k)) n
    rw [(actionReduction_apply_same z k t).1]
    by_cases hn : n = k <;> simp [lp.single_apply,hn]
  · change (lp.single (E := fun _ : ℤ => ℝ) p k ((actionReduction z k t).2 k)) n =
      actionReductionScale (pairAction z k) t*(lp.single (E := fun _ : ℤ => ℝ) p k (z.2 k)) n
    rw [(actionReduction_apply_same z k t).2]
    by_cases hn : n = k <;> simp [lp.single_apply,hn]

/-- The explicit curve solves the autonomous radial differential equation. -/
theorem hasDerivAt_actionReduction_vector (z : RealCoeff p × RealCoeff p) (k : ℤ)
    (ha : 0 < pairAction z k) {t : ℝ} (ht : t < pairAction z k) :
    HasDerivAt (actionReduction z k) (actionReductionVector (actionReduction z k t) k) t := by
  have hpos : 0 < 1-t/pairAction z k := by
    have := (div_lt_one ha).mpr ht
    linarith
  have hr : 0 < actionReductionScale (pairAction z k) t := Real.sqrt_pos.mpr hpos
  have hsq : (actionReductionScale (pairAction z k) t)^2 = 1-t/pairAction z k :=
    Real.sq_sqrt hpos.le
  have he : -(1/pairAction z k)/(2*actionReductionScale (pairAction z k) t) =
      -(1/(2*(pairAction z k-t)))*actionReductionScale (pairAction z k) t := by
    have hmul : (actionReductionScale (pairAction z k) t)^2*pairAction z k = pairAction z k-t := by
      rw [hsq]; field_simp
    field_simp [ne_of_gt ha,ne_of_gt hr,ne_of_gt (sub_pos.mpr ht)]
    nlinarith
  rw [actionReductionVector,pairAction_actionReduction_same z k ha t ht.le,
    pairMode_actionReduction,smul_smul,← he]
  exact hasDerivAt_actionReduction z k ha ht

end NLS.RealCoeff
