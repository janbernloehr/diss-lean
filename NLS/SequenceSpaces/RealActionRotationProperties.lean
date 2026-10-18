import NLS.SequenceSpaces.RealActionRotation

/-! # Commutation and continuity of real action rotations

Rotations in arbitrary coordinate pairs commute, including repeated indices.
Joint continuity in time and the initial sequence holds in every Banach lp
space, including the infinity exponent.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.RealCoeff

variable {p : ℝ≥0∞}

/-- Any two action-coordinate rotations commute, including repeated indices. -/
theorem actionRotation_comm (z : RealCoeff p × RealCoeff p) (k l : ℤ) (t r : ℝ) :
    actionRotation (actionRotation z k t) l r = actionRotation (actionRotation z l r) k t := by
  by_cases hkl : k = l
  · subst l
    rw [actionRotation_add,actionRotation_add,add_comm]
  · apply Prod.ext <;> ext n
    · by_cases hn : n = k
      · subst n
        rw [(actionRotation_apply_ne _ l k hkl r).1,(actionRotation_apply_same _ k t).1,
          (actionRotation_apply_same _ k t).1,(actionRotation_apply_ne z l k hkl r).1,
          (actionRotation_apply_ne z l k hkl r).2]
      · by_cases hl : n = l
        · subst n
          rw [(actionRotation_apply_same _ l r).1,(actionRotation_apply_ne z k l hn t).1,
            (actionRotation_apply_ne z k l hn t).2,(actionRotation_apply_ne _ k l hn t).1,
            (actionRotation_apply_same z l r).1]
        · rw [(actionRotation_apply_ne _ l n hl r).1,(actionRotation_apply_ne _ k n hn t).1,
            (actionRotation_apply_ne _ k n hn t).1,(actionRotation_apply_ne _ l n hl r).1]
    · by_cases hn : n = k
      · subst n
        rw [(actionRotation_apply_ne _ l k hkl r).2,(actionRotation_apply_same _ k t).2,
          (actionRotation_apply_same _ k t).2,(actionRotation_apply_ne z l k hkl r).1,
          (actionRotation_apply_ne z l k hkl r).2]
      · by_cases hl : n = l
        · subst n
          rw [(actionRotation_apply_same _ l r).2,(actionRotation_apply_ne z k l hn t).1,
            (actionRotation_apply_ne z k l hn t).2,(actionRotation_apply_ne _ k l hn t).2,
            (actionRotation_apply_same z l r).2]
        · rw [(actionRotation_apply_ne _ l n hl r).2,(actionRotation_apply_ne _ k n hn t).2,
            (actionRotation_apply_ne _ k n hn t).2,(actionRotation_apply_ne _ l n hl r).2]


variable [Fact (1 ≤ p)]

/-- The one-coordinate rotation depends continuously on both time and initial sequence. -/
theorem continuous_actionRotation (k : ℤ) :
    Continuous (fun z : ℝ × (RealCoeff p × RealCoeff p) => actionRotation z.2 k z.1) := by
  let S := lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℝ) p k
  let E := lp.evalCLM ℝ (fun _ : ℤ => ℝ) p k
  have hx : Continuous (fun z : RealCoeff p × RealCoeff p => lp.single (E := fun _ : ℤ => ℝ) p k (z.1 k)) := by
    convert! ((S.comp E).comp (ContinuousLinearMap.fst ℝ (RealCoeff p) (RealCoeff p))).continuous using 1
  have hy : Continuous (fun z : RealCoeff p × RealCoeff p => lp.single (E := fun _ : ℤ => ℝ) p k (z.2 k)) := by
    convert! ((S.comp E).comp (ContinuousLinearMap.snd ℝ (RealCoeff p) (RealCoeff p))).continuous using 1
  have hm : Continuous (fun z : RealCoeff p × RealCoeff p => pairMode z k) := hx.prodMk hy
  have hv : Continuous (fun z : RealCoeff p × RealCoeff p => actionRotationVector z k) := hy.neg.prodMk hx
  exact (continuous_snd.add (((Real.continuous_cos.comp continuous_fst).sub continuous_const).smul
    (hm.comp continuous_snd))).add ((Real.continuous_sin.comp continuous_fst).smul (hv.comp continuous_snd))

end NLS.RealCoeff
