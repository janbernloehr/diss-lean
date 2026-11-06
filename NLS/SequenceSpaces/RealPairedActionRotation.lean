import NLS.SequenceSpaces.RealActionRotationProperties

/-! # Opposite rotations in two real action planes

The two selected indices may coincide, in which case the action is the
identity. At distinct indices the derivative is exactly the difference
of the two original rotation fields, with no open-action hypothesis.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞}

def pairedActionRotation (z : RealCoeff p × RealCoeff p) (k l : ℤ) (t : ℝ) :
    RealCoeff p × RealCoeff p := actionRotation (actionRotation z k t) l (-t)

theorem pairMode_actionRotation_ne (z : RealCoeff p × RealCoeff p) (k l : ℤ)
    (hl : l ≠ k) (t : ℝ) : pairMode (actionRotation z k t) l = pairMode z l := by
  simp only [pairMode,(actionRotation_apply_ne z k l hl t).1,(actionRotation_apply_ne z k l hl t).2]

theorem actionRotationVector_actionRotation_ne (z : RealCoeff p × RealCoeff p) (k l : ℤ)
    (hl : l ≠ k) (t : ℝ) : actionRotationVector (actionRotation z k t) l = actionRotationVector z l := by
  simp only [actionRotationVector,(actionRotation_apply_ne z k l hl t).1,(actionRotation_apply_ne z k l hl t).2]

theorem pairedActionRotation_explicit (z : RealCoeff p × RealCoeff p) (k l : ℤ)
    (hkl : k ≠ l) (t : ℝ) :
    pairedActionRotation z k l t = z+(Real.cos t-1) • (pairMode z k+pairMode z l)+
      Real.sin t • (actionRotationVector z k-actionRotationVector z l) := by
  rw [pairedActionRotation,actionRotation,Real.cos_neg,Real.sin_neg,
    pairMode_actionRotation_ne z k l hkl.symm,
    actionRotationVector_actionRotation_ne z k l hkl.symm]
  unfold actionRotation
  simp only [smul_add,smul_sub,neg_smul]
  abel

@[simp] theorem pairedActionRotation_zero (z : RealCoeff p × RealCoeff p) (k l : ℤ) :
    pairedActionRotation z k l 0 = z := by simp [pairedActionRotation]

@[simp] theorem pairedActionRotation_same (z : RealCoeff p × RealCoeff p) (k : ℤ) (t : ℝ) :
    pairedActionRotation z k k t = z := by simp [pairedActionRotation,actionRotation_add]

theorem pairedActionRotation_action (z : RealCoeff p × RealCoeff p) (k l n : ℤ) (t : ℝ) :
    pairAction (pairedActionRotation z k l t) n = pairAction z n := by
  simp only [pairedActionRotation,pairAction_actionRotation]

variable [Fact (1 ≤ p)]

theorem actionRotationVector_actionRotation_same (z : RealCoeff p × RealCoeff p) (k : ℤ) (t : ℝ) :
    actionRotationVector (actionRotation z k t) k =
      (-Real.sin t) • pairMode z k+Real.cos t • actionRotationVector z k := by
  have hd := ((((Real.hasDerivAt_cos t).sub_const 1).smul_const (pairMode z k)).const_add z).add
    ((Real.hasDerivAt_sin t).smul_const (actionRotationVector z k))
  change HasDerivAt (actionRotation z k) _ t at hd
  exact ((hasDerivAt_actionRotation z k t).unique hd)

theorem hasDerivAt_pairedActionRotation (z : RealCoeff p × RealCoeff p) (k l : ℤ) (t : ℝ) :
    HasDerivAt (pairedActionRotation z k l)
      (actionRotationVector (pairedActionRotation z k l t) k-
        actionRotationVector (pairedActionRotation z k l t) l) t := by
  by_cases hkl : k = l
  · subst l
    have he : pairedActionRotation z k k = fun _ => z :=
      funext (fun r => pairedActionRotation_same z k r)
    rw [he,sub_self]
    exact hasDerivAt_const t z
  have hd := ((((Real.hasDerivAt_cos t).sub_const 1).smul_const (pairMode z k+pairMode z l)).const_add z).add
    ((Real.hasDerivAt_sin t).smul_const (actionRotationVector z k-actionRotationVector z l))
  change HasDerivAt (fun r => z+(Real.cos r-1) • (pairMode z k+pairMode z l)+
    Real.sin r • (actionRotationVector z k-actionRotationVector z l)) _ t at hd
  have hfun : (fun r => z+(Real.cos r-1) • (pairMode z k+pairMode z l)+
      Real.sin r • (actionRotationVector z k-actionRotationVector z l)) = pairedActionRotation z k l :=
    funext (fun r => (pairedActionRotation_explicit z k l hkl r).symm)
  rw [hfun] at hd
  convert! hd using 1
  rw [pairedActionRotation,actionRotationVector_actionRotation_ne _ l k hkl,
    actionRotationVector_actionRotation_same,actionRotationVector_actionRotation_same,
    pairMode_actionRotation_ne z k l (Ne.symm hkl),
    actionRotationVector_actionRotation_ne z k l (Ne.symm hkl),Real.cos_neg,Real.sin_neg,neg_neg]
  simp only [smul_add,smul_sub,neg_smul]
  abel

theorem continuous_pairedActionRotation (k l : ℤ) :
    Continuous (fun z : ℝ × (RealCoeff p × RealCoeff p) => pairedActionRotation z.2 k l z.1) :=
  (continuous_actionRotation l).comp
    (continuous_fst.neg.prodMk (continuous_actionRotation k))

end NLS.RealCoeff
