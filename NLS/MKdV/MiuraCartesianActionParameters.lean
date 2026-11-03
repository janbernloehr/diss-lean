import NLS.MKdV.MiuraCartesianRotations
import NLS.SequenceSpaces.PositiveCartesianParameters
import NLS.SequenceSpaces.TailSumCoordinates
import NLS.SequenceSpaces.MixedSquare

/-! # The normalized tail quotient is the physical action and signed mean

The zero head retains the mean without squaring it. Positive tail sums
are exactly twice the weighted physical actions in their native l1 norm.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

abbrev MiuraActionMeanTarget := WeightedCoeff (Weight.sobolev 1) 1 × ℂ

def miuraActionTailParameters : MiuraActionMeanTarget →L[ℂ] Coeff.TailSumSpace 1 {0} :=
  (ContinuousLinearMap.pi fun _ => ContinuousLinearMap.snd ℂ _ ℂ).prod
    ((2 : ℂ) • ((WeightedCoeff.weightIsometry (Weight.sobolev 1) 1).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℂ _ ℂ)))

@[simp] theorem miuraActionTailParameters_head (b : MiuraActionMeanTarget) (k : ({0} : Finset ℤ)) :
    (miuraActionTailParameters b).1 k = b.2 := rfl

@[simp] theorem miuraActionTailParameters_tail (b : MiuraActionMeanTarget) (n : ℤ) :
    (miuraActionTailParameters b).2 n = 2*(Weight.sobolev 1 n : ℂ)*b.1.val n := by
  change 2*((Weight.sobolev 1 n : ℂ)*b.1.val n) = _
  ring

def miuraPositiveCartesianActionMean (z : MiuraPositiveCartesianTarget) : MiuraActionMeanTarget :=
  (miuraL2CartesianActions (z.1.1.val,z.1.2.val),z.2)

/-- The abstract tail quotient has precisely the required physical
normalization. Both zero actions and zero signed mean are included. -/
theorem miuraCartesian_tail_parameters (z : MiuraPositiveCartesianTarget) :
    Coeff.tailSumCLM {0} (Coeff.pairMixedSquare (q := 1) {0}
      (WeightedCoeff.positiveCartesianParameterSection (Weight.sobolev (1/2)) 2 z)) =
      miuraActionTailParameters (miuraPositiveCartesianActionMean z) := by
  classical
  apply Prod.ext
  · funext k
    have hk : k.val = 0 := Finset.mem_singleton.mp k.property
    change Coeff.mixedSquare (q := 1) {0}
      (WeightedCoeff.positiveCartesianParameterSection (Weight.sobolev (1/2)) 2 z).1 k.val = z.2
    rw [Coeff.mixedSquare_apply,if_pos k.property,WeightedCoeff.positiveCartesianParameterSection_fst,hk,
      z.1.1.property 0 le_rfl]
    simp
  · ext n
    change (Coeff.mixedSquare (q := 1) {0}
      (WeightedCoeff.positiveCartesianParameterSection (Weight.sobolev (1/2)) 2 z).2 n)+
      (Coeff.mixedSquare (q := 1) {0}
        (WeightedCoeff.positiveCartesianParameterSection (Weight.sobolev (1/2)) 2 z).1 n-
        Coeff.truncate {0} (Coeff.mixedSquare (q := 1) {0}
          (WeightedCoeff.positiveCartesianParameterSection (Weight.sobolev (1/2)) 2 z).1) n) = _
    rw [miuraActionTailParameters_tail]
    simp only [miuraPositiveCartesianActionMean,miuraL2CartesianActions_apply]
    simp only [Coeff.mixedSquare_apply,Coeff.truncate_apply,Finset.mem_singleton,
      WeightedCoeff.positiveCartesianParameterSection_fst,WeightedCoeff.positiveCartesianParameterSection_snd]
    by_cases hn : n = 0
    · subst n
      rw [z.1.1.property 0 le_rfl,z.1.2.property 0 le_rfl]
      simp
    · simp only [if_neg hn,add_zero,sub_zero]
      have hw : (Weight.sobolev (1/2) n : ℂ)^2 = (Weight.sobolev 1 n : ℂ) := by
        have hreal : Weight.sobolev (1/2) n*Weight.sobolev (1/2) n = Weight.sobolev 1 n := by
          rw [Weight.sobolev_apply,← Real.rpow_add (by positivity)]
          norm_num
        simpa only [pow_two,Complex.ofReal_mul] using congrArg (fun x : ℝ => (x : ℂ)) hreal
      rw [mul_pow,mul_pow,hw]
      ring

/-- The positive Cartesian radius map recovers all actual original L2
actions together with the literal signed mean. -/
theorem miuraPositiveCartesianActionMean_map (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    miuraPositiveCartesianActionMean (miuraPositiveCartesianMap a) = miuraL2ActionMeanMap a := by
  have he : ((miuraPositiveCartesianMap a).1.1.val,(miuraPositiveCartesianMap a).1.2.val) =
      miuraL2CartesianSequence a := by
    apply Prod.ext <;> apply Subtype.ext <;> funext n
    · change (WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence a).1).val.val n = _
      rw [WeightedCoeff.positiveProjection_apply]
      split_ifs with hn
      · rfl
      · exact (congrArg Prod.fst (miuraL2CartesianSequence_nonpositive a ha n hn)).symm
    · change (WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence a).2).val.val n = _
      rw [WeightedCoeff.positiveProjection_apply]
      split_ifs with hn
      · rfl
      · exact (congrArg Prod.snd (miuraL2CartesianSequence_nonpositive a ha n hn)).symm
  apply Prod.ext
  · change miuraL2CartesianActions _ = miuraL2ActionSequence a
    rw [he,miuraL2CartesianActions_sequence_eq a ha]
  · rfl

end NLS.MKdV
