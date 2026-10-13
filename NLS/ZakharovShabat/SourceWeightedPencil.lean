import NLS.ZakharovShabat.SourceWeightedGapAsymptotics
import NLS.ZakharovShabat.WeightedDomainPotential

/-!
# The original spectral pencil on weighted input and domain

Forgetting the spectral weight preserves both raw Fourier components in the
base and derivative spaces. The resulting original pencil is exactly the
weighted free pencil minus the actual weighted potential.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted derivative domain included into the original source domain. -/
def sourceWeightedDomainInput (w : SpectralWeight) :
    WeightedDomain w.toWeight p →L[ℂ] WeightedCoeffPair (Weight.sobolev 1) p :=
  (WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm.toContinuousLinearMap.comp
    (weightedDomainToDomain w)

@[simp] theorem sourceWeightedDomainInput_fst (w : SpectralWeight)
    (f : WeightedDomain w.toWeight p) (k : ℤ) :
    (sourceWeightedDomainInput w f).fst.val k = f.fst.val k := weightedDomainToDomain_fst w f k

@[simp] theorem sourceWeightedDomainInput_snd (w : SpectralWeight)
    (f : WeightedDomain w.toWeight p) (k : ℤ) :
    (sourceWeightedDomainInput w f).snd.val k = f.snd.val k := weightedDomainToDomain_snd w f k

theorem toMax_sourceWeightedDomainInput (w : SpectralWeight) (f : WeightedDomain w.toWeight p) :
    WeightedCoeffPair.toMax (Weight.sobolev 1) p (sourceWeightedDomainInput w f) = weightedDomainToDomain w f :=
  ContinuousLinearEquiv.apply_symm_apply _ _

theorem sourceWeightedPeriodTwoInput_injective (w : SpectralWeight) :
    Function.Injective (sourceWeightedPeriodTwoInput (p := p) w) := by
  intro f g h
  apply weightedPair_ext
  · intro k; simpa only [sourceWeightedPeriodTwoInput_fst] using congrArg (fun a => a.fst k) h
  · intro k; simpa only [sourceWeightedPeriodTwoInput_snd] using congrArg (fun a => a.snd k) h

theorem sourceWeightedDomainInput_injective (w : SpectralWeight) :
    Function.Injective (sourceWeightedDomainInput (p := p) w) := by
  intro f g h
  apply weightedPair_ext
  · intro k; simpa only [sourceWeightedDomainInput_fst] using congrArg (fun a => a.fst.val k) h
  · intro k; simpa only [sourceWeightedDomainInput_snd] using congrArg (fun a => a.snd.val k) h

/-- Forgetting the weight commutes with actual domain inclusion. -/
theorem sourceWeightedDomainInput_inclusion (w : SpectralWeight) (f : WeightedDomain w.toWeight p) :
    sourceDomainInclusion (sourceWeightedDomainInput w f) = sourceWeightedPeriodTwoInput w (weightedDomainInclusion w.toWeight f) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext k <;> simp

/-- The weighted potential is precisely the potential part of the original source operator. -/
theorem sourceWeightedDomainPotential_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (f : WeightedDomain w.toWeight p) :
    sourceWeightedPeriodTwoInput w (weightedDomainPotential hp w φ f) =
      sourceOperator hp (sourceWeightedPeriodTwoInput w φ) (sourceWeightedDomainInput w f) -
        sourceOperator hp 0 (sourceWeightedDomainInput w f) := by
  change (CoeffPair.toMax p).symm (weightedBaseToPair w (weightedDomainPotential hp w φ f)) =
    (CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p (sourceWeightedPeriodTwoInput w φ))
      (WeightedCoeffPair.toMax (Weight.sobolev 1) p (sourceWeightedDomainInput w f))) -
    (CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p 0)
      (WeightedCoeffPair.toMax (Weight.sobolev 1) p (sourceWeightedDomainInput w f)))
  rw [toMax_sourceWeightedPeriodTwoInput,toMax_sourceWeightedDomainInput,map_zero,operator_zero,
    ← map_sub,weightedDomainPotential_eq_original]
  congr 1
  change _ = freeOperator _ + potentialOperator hp _ _ - freeOperator _
  abel

/-- Exact original-source realization of the full weighted differential pencil. -/
theorem sourceWeightedPencil_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (z : ℂ) (f : WeightedDomain w.toWeight p) :
    sourceSpectralPencil hp (sourceWeightedPeriodTwoInput w φ) z (sourceWeightedDomainInput w f) =
      sourceWeightedPeriodTwoInput w (weightedFreePencil w.toWeight z f - weightedDomainPotential hp w φ f) := by
  change (CoeffPair.toMax p).symm (spectralPencil hp (CoeffPair.toMax p (sourceWeightedPeriodTwoInput w φ)) z
    (WeightedCoeffPair.toMax (Weight.sobolev 1) p (sourceWeightedDomainInput w f))) =
      (CoeffPair.toMax p).symm (weightedBaseToPair w (_ - _))
  rw [toMax_sourceWeightedPeriodTwoInput,toMax_sourceWeightedDomainInput,map_sub,
    weightedFreePencil_eq_original,weightedDomainPotential_eq_original,spectralPencil_apply]
  congr 1
  change _ - (freeOperator _ + potentialOperator hp _ _) = _
  abel

/-- The weighted free pencil agrees with the original zero-potential pencil. -/
theorem sourceWeightedFreePencil_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (z : ℂ) (f : WeightedDomain w.toWeight p) :
    sourceSpectralPencil hp 0 z (sourceWeightedDomainInput w f) =
      sourceWeightedPeriodTwoInput w (weightedFreePencil w.toWeight z f) := by
  have hzero : weightedDomainPotential hp w (0 : WeightedCoeffPair w.toWeight p) = 0 := by
    ext g : 1
    apply weightedPair_ext <;> intro k <;> simp
  simpa only [map_zero,hzero,zero_apply,sub_zero] using sourceWeightedPencil_eq hp w 0 z f

/-- Vanishing of the original pencil is equivalent to the actual weighted eigenvalue equation. -/
theorem sourceWeightedPencil_zero_iff (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (z : ℂ) (f : WeightedDomain w.toWeight p) :
    sourceSpectralPencil hp (sourceWeightedPeriodTwoInput w φ) z (sourceWeightedDomainInput w f) = 0 ↔
      weightedFreePencil w.toWeight z f = weightedDomainPotential hp w φ f := by
  rw [sourceWeightedPencil_eq,← map_zero (sourceWeightedPeriodTwoInput (p := p) w),
    (sourceWeightedPeriodTwoInput_injective w).eq_iff,sub_eq_zero]

/-- The original source eigenvalue equation has the same weighted P/Q formulation. -/
theorem sourceWeighted_eigenvalue_iff (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (z : ℂ) (f : WeightedDomain w.toWeight p) :
    sourceOperator hp (sourceWeightedPeriodTwoInput w φ) (sourceWeightedDomainInput w f) =
      z • sourceDomainInclusion (sourceWeightedDomainInput w f) ↔
        weightedFreePencil w.toWeight z f = weightedDomainPotential hp w φ f := by
  rw [← sourceWeightedPencil_zero_iff hp w φ z f,sourceSpectralPencil_eq]
  rw [sub_apply,smul_apply,sub_eq_zero,eq_comm]

end NLS.ZakharovShabat
