import NLS.SequenceSpaces.PositiveQuadraticMeanParameters
import NLS.MKdV.MiuraCartesianActionParameters

/-! # The auxiliary full action sequence is exactly physical actions plus signed mean

The positive entries are the native weighted physical actions. The zero
entry is the signed mean itself, using the entire isotropic section.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV
local instance : (2 : ℝ≥0∞).HolderTriple 2 1 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

def miuraActionQuadraticParameters : MiuraActionMeanTarget →L[ℂ] Coeff 1 :=
  (WeightedCoeff.positiveToCoeff (Weight.sobolev 1) 1).comp
    ((WeightedCoeff.positiveProjection (Weight.sobolev 1) 1).comp (ContinuousLinearMap.fst ℂ _ ℂ))+
      (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 1 0).comp (ContinuousLinearMap.snd ℂ _ ℂ)

theorem miuraActionQuadraticParameters_apply (b : MiuraActionMeanTarget) (n : ℤ) :
    miuraActionQuadraticParameters b n =
      (if 0 < n then (Weight.sobolev 1 n : ℂ)*b.1.val n else 0)+(if n = 0 then b.2 else 0) := by
  change (Weight.sobolev 1 n : ℂ)*
    (WeightedCoeff.positiveProjection (Weight.sobolev 1) 1 b.1).val.val n+
      (lp.single (E := fun _ : ℤ => ℂ) 1 0 b.2) n = _
  rw [WeightedCoeff.positiveProjection_apply]
  by_cases hn : 0 < n <;> simp [lp.single_apply,Pi.single_apply,hn]

/-- Full quadratic action descent in the auxiliary parameters retains
the actual signed mean linearly and the exact native physical actions. -/
theorem miuraCartesian_quadratic_parameters (z : MiuraPositiveCartesianTarget) :
    quadraticActionsExponent (q := 1)
      (WeightedCoeff.positiveCartesianIsotropicSection (Weight.sobolev (1/2)) z) =
        miuraActionQuadraticParameters (miuraPositiveCartesianActionMean z) := by
  ext n
  by_cases hz : n = 0
  · subst n
    have hmean := congrArg Prod.snd
      (WeightedCoeff.positiveCartesianQuadraticMeanMap_isotropicSection (Weight.sobolev (1/2)) z)
    change Coeff.zeroPairRadius (WeightedCoeff.positiveCartesianIsotropicSection (Weight.sobolev (1/2)) z) = z.2 at hmean
    rw [quadraticActionsExponent_apply]
    change Coeff.zeroPairRadius (WeightedCoeff.positiveCartesianIsotropicSection (Weight.sobolev (1/2)) z) =
      miuraActionQuadraticParameters (miuraPositiveCartesianActionMean z) 0
    have hb : miuraActionQuadraticParameters (miuraPositiveCartesianActionMean z) 0 = z.2 := by
      rw [miuraActionQuadraticParameters_apply]
      simp
      rfl
    rw [hb]
    exact hmean
  · rw [quadraticActionsExponent_apply,WeightedCoeff.positiveCartesianIsotropicSection_fst,
      WeightedCoeff.positiveCartesianIsotropicSection_snd,if_neg hz,if_neg hz,add_zero,add_zero,
      miuraActionQuadraticParameters_apply,if_neg hz,add_zero]
    by_cases hn : 0 < n
    · rw [if_pos hn]
      simp only [miuraPositiveCartesianActionMean,miuraL2CartesianActions_apply]
      have hw : (Weight.sobolev (1/2) n : ℂ)^2 = (Weight.sobolev 1 n : ℂ) := by
        have he : Weight.sobolev (1/2) n*Weight.sobolev (1/2) n = Weight.sobolev 1 n := by
          rw [Weight.sobolev_apply,← Real.rpow_add (by positivity)]
          norm_num
        simpa only [pow_two,Complex.ofReal_mul] using congrArg (fun t : ℝ => (t : ℂ)) he
      rw [mul_pow,mul_pow,hw]
      ring
    · rw [if_neg hn,z.1.1.property n (by omega),z.1.2.property n (by omega)]
      ring

end NLS.MKdV
