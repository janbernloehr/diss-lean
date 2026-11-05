import NLS.SequenceSpaces.PositiveWeightedCoefficients
import NLS.ComplexAnalysis.CartesianPlaneRotation
import NLS.ComplexAnalysis.LinearRotationDerivative

/-! # Bounded native Cartesian rotations in a positive weighted sequence target -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

abbrev PositiveCartesianTarget := (positiveSubmodule w p × positiveSubmodule w p) × ℂ

def positiveModeCLM (k : ℤ) : positiveSubmodule w p →L[ℂ] positiveSubmodule w p :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨truncate w p {k} a.val,by
        intro n hn
        rw [truncate_apply]
        split_ifs
        · exact a.property n hn
        · rfl⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        apply Subtype.ext
        funext n
        change (truncate w p {k} (a.val+b.val)).val n =
          (truncate w p {k} a.val).val n+(truncate w p {k} b.val).val n
        simp only [truncate_apply]
        split_ifs
        · rfl
        · simp only [add_zero]
      map_smul' := by
        intro c a
        apply Subtype.ext
        apply Subtype.ext
        funext n
        change (truncate w p {k} (c • a.val)).val n = c*(truncate w p {k} a.val).val n
        simp only [truncate_apply]
        split_ifs <;> simp only [smul_val,mul_zero] }
    1 (by intro a; change ‖truncate w p {k} a.val‖ ≤ 1*‖a.val‖; simpa only [one_mul] using norm_truncate_le w p {k} a.val)

@[simp] theorem positiveModeCLM_apply (k : ℤ) (a : positiveSubmodule w p) (n : ℤ) :
    (positiveModeCLM w p k a).val.val n = if n = k then a.val.val n else 0 := by
  change (truncate w p {k} a.val).val n = _
  simp only [truncate_apply,Finset.mem_singleton]

def positiveCartesianEval (n : ℤ) : PositiveCartesianTarget w p →L[ℂ] (ℂ × ℂ) :=
  let e := (evalCLM w p n).comp (positiveSubmodule w p).subtypeL
  let f := ContinuousLinearMap.fst ℂ (positiveSubmodule w p × positiveSubmodule w p) ℂ
  ((e.comp (ContinuousLinearMap.fst ℂ _ _)).comp f).prod ((e.comp (ContinuousLinearMap.snd ℂ _ _)).comp f)

@[simp] theorem positiveCartesianEval_apply (n : ℤ) (z : PositiveCartesianTarget w p) :
    positiveCartesianEval w p n z = (z.1.1.val.val n,z.1.2.val.val n) := rfl

def positiveCartesianMode (k : ℤ) : PositiveCartesianTarget w p →L[ℂ] PositiveCartesianTarget w p :=
  (((positiveModeCLM w p k).prodMap (positiveModeCLM w p k)).comp
    (ContinuousLinearMap.fst ℂ _ ℂ)).prod 0

def positiveCartesianActionVector (k : ℤ) : PositiveCartesianTarget w p →L[ℂ] PositiveCartesianTarget w p :=
  let P := positiveModeCLM w p k
  (((P.comp (ContinuousLinearMap.snd ℂ (positiveSubmodule w p) (positiveSubmodule w p))).prod (-(P.comp (ContinuousLinearMap.fst ℂ (positiveSubmodule w p) (positiveSubmodule w p))))).comp
    (ContinuousLinearMap.fst ℂ _ ℂ)).prod 0

theorem positiveCartesianMode_eval (k n : ℤ) (z : PositiveCartesianTarget w p) :
    positiveCartesianEval w p n (positiveCartesianMode w p k z) =
      if n = k then positiveCartesianEval w p n z else 0 := by
  change ((positiveModeCLM w p k z.1.1).val.val n,(positiveModeCLM w p k z.1.2).val.val n) = _
  rw [positiveModeCLM_apply,positiveModeCLM_apply]
  split_ifs <;> rfl

theorem positiveCartesianActionVector_eval (k n : ℤ) (z : PositiveCartesianTarget w p) :
    positiveCartesianEval w p n (positiveCartesianActionVector w p k z) =
      if n = k then ((positiveCartesianEval w p n z).2,-(positiveCartesianEval w p n z).1) else 0 := by
  change ((positiveModeCLM w p k z.1.2).val.val n,-(positiveModeCLM w p k z.1.1).val.val n) = _
  rw [positiveModeCLM_apply,positiveModeCLM_apply]
  by_cases hn : n = k
  · simp only [if_pos hn]
    rfl
  · simp only [if_neg hn,neg_zero]
    rfl

def positiveCartesianRotation (k : ℤ) (t : ℝ) : PositiveCartesianTarget w p →L[ℂ] PositiveCartesianTarget w p :=
  ContinuousLinearMap.id ℂ _+((Real.cos t : ℂ)-1) • positiveCartesianMode w p k+
    (Real.sin t : ℂ) • positiveCartesianActionVector w p k

theorem positiveCartesianRotation_apply (k : ℤ) (t : ℝ) (z : PositiveCartesianTarget w p) :
    positiveCartesianRotation w p k t z = z+((Real.cos t : ℂ)-1) • positiveCartesianMode w p k z+
      (Real.sin t : ℂ) • positiveCartesianActionVector w p k z := rfl

theorem positiveCartesianRotation_eval (k n : ℤ) (t : ℝ) (z : PositiveCartesianTarget w p) :
    positiveCartesianEval w p n (positiveCartesianRotation w p k t z) =
      if n = k then cartesianPlaneRotation t (positiveCartesianEval w p n z) else positiveCartesianEval w p n z := by
  rw [positiveCartesianRotation_apply,map_add,map_add,map_smul,map_smul,
    positiveCartesianMode_eval,positiveCartesianActionVector_eval]
  split_ifs
  · apply Prod.ext
    · change (positiveCartesianEval w p n z).1+((Real.cos t : ℂ)-1)*(positiveCartesianEval w p n z).1+
        (Real.sin t : ℂ)*(positiveCartesianEval w p n z).2 = _
      change _ = (Real.cos t : ℂ)*(positiveCartesianEval w p n z).1+(Real.sin t : ℂ)*(positiveCartesianEval w p n z).2
      ring
    · change (positiveCartesianEval w p n z).2+((Real.cos t : ℂ)-1)*(positiveCartesianEval w p n z).2+
        (Real.sin t : ℂ)*(-(positiveCartesianEval w p n z).1) = _
      change _ = -(Real.sin t : ℂ)*(positiveCartesianEval w p n z).1+(Real.cos t : ℂ)*(positiveCartesianEval w p n z).2
      ring
  · simp only [smul_zero,add_zero]

theorem positiveCartesianRotation_mean (k : ℤ) (t : ℝ) (z : PositiveCartesianTarget w p) :
    (positiveCartesianRotation w p k t z).2 = z.2 := by
  change z.2+((Real.cos t : ℂ)-1)*0+(Real.sin t : ℂ)*0 = z.2
  ring

@[simp] theorem positiveCartesianRotation_zero (k : ℤ) (z : PositiveCartesianTarget w p) :
    positiveCartesianRotation w p k 0 z = z := by simp [positiveCartesianRotation_apply]

theorem hasDerivAt_positiveCartesianRotation_zero (k : ℤ) (z : PositiveCartesianTarget w p) :
    HasDerivAt (fun t => positiveCartesianRotation w p k t z) (positiveCartesianActionVector w p k z) 0 :=
  hasDerivAt_linear_rotation_zero z (positiveCartesianMode w p k z) (positiveCartesianActionVector w p k z)

end NLS.WeightedCoeff
