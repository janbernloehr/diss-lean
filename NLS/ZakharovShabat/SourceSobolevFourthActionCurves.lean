import NLS.ZakharovShabat.SourceSobolevFourthActions
import NLS.ZakharovShabat.SourceSobolevFourthFrequency
import NLS.SequenceSpaces.WeightedSingle

/-! # Exact physical H₄ action curves in the original weighted action space

The reduction parameter changes the raw selected action at unit speed. At a
closed mode, the opening amplitude changes that action by precisely t²/2.
Both identities hold in the full ell^(3,1) norm, not just coordinatewise.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The raw unit action direction, including its original order-three weight. -/
def fourthSobolevActionDirection (n : ℤ) : FourthSobolevActions :=
  WeightedCoeff.single fourthSobolevActionWeight n 1

/-- Before the selected action collapses, its full weighted sequence follows
the original affine unit-speed line. -/
theorem fourthSobolevActions_actionReduction
    (z : FourthSobolevBirkhoffTarget) (n : ℤ)
    (ha : 0 < RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight z) n)
    (t : ℝ) (ht : t ≤ RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight z) n) :
    fourthSobolevActions (WeightedRealCoeff.actionReduction
      (sourceFrequencyWeight fourthSobolevSpectralWeight)
      (fun k => fourthSobolevSpectralWeight.one_le (2*k)) z n t) =
        fourthSobolevActions z - (t:ℂ) • fourthSobolevActionDirection n := by
  apply Subtype.ext
  funext k
  rw [fourthSobolevActions_apply,WeightedCoeff.sub_val,WeightedCoeff.smul_val,
    fourthSobolevActions_apply,fourthSobolevActionDirection,WeightedCoeff.single_val]
  by_cases hkn : k = n
  · subst k
    erw [WeightedRealCoeff.pairAction_actionReduction_same _ _ z n ha t ht]
    simp
    rfl
  · erw [WeightedRealCoeff.pairAction_actionReduction_ne _ _ z n k hkn t]
    simp [Pi.single_eq_of_ne hkn]
    rfl

/-- A closed raw mode opens along the exact quadratic action line, in the
original weighted action Banach space. -/
theorem fourthSobolevActions_actionOpening
    (z : FourthSobolevBirkhoffTarget) (n : ℤ)
    (hz : (originalWeightedRealTarget fourthSobolevSpectralWeight z).1 n = 0 ∧
      (originalWeightedRealTarget fourthSobolevSpectralWeight z).2 n = 0) (t : ℝ) :
    fourthSobolevActions (NLS.Birkhoff.weightedActionOpening
      (sourceFrequencyWeight fourthSobolevSpectralWeight) z n t) =
        fourthSobolevActions z + ((t^2/2:ℝ):ℂ) • fourthSobolevActionDirection n := by
  apply Subtype.ext
  funext k
  rw [fourthSobolevActions_apply,WeightedCoeff.add_val,WeightedCoeff.smul_val,
    fourthSobolevActions_apply,fourthSobolevActionDirection,WeightedCoeff.single_val]
  have he : originalWeightedRealTarget fourthSobolevSpectralWeight
      (NLS.Birkhoff.weightedActionOpening (sourceFrequencyWeight fourthSobolevSpectralWeight) z n t) =
      RealCoeff.actionOpening (originalWeightedRealTarget fourthSobolevSpectralWeight z) n t :=
    NLS.Birkhoff.forget_weightedActionOpening _ (fun k => fourthSobolevSpectralWeight.one_le (2*k)) z n t
  rw [he]
  by_cases hkn : k = n
  · subst k
    rw [RealCoeff.pairAction_actionOpening_same _ n hz t]
    have hzero : RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight z) n = 0 := by
      simp [RealCoeff.pairAction,hz.1,hz.2]
    simp [hzero]
  · rw [RealCoeff.pairAction_actionOpening_ne _ n k hkn t]
    simp [Pi.single_eq_of_ne hkn]

end NLS.ZakharovShabat
