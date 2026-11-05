import NLS.ZakharovShabat.ContinuousPotentialL2Bound
import NLS.ZakharovShabat.SourcePhysicalRealL2
import NLS.ZakharovShabat.L2Discriminant

/-! # The original Fourier source of a continuous physical interval pair

The bounded map is the inverse physical Fourier isometry applied to the
actual L² class. Its discriminant and real type are proved physical
identifications, independent of a choice of null-set representative.
-/
noncomputable section
open scoped ComplexConjugate
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

def continuousPotentialSource : Curve (ℂ × ℂ) →L[ℂ] CoeffPair 2 :=
  sourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    continuousPotentialL2CLM

theorem canonicalDiscriminant_continuousPotentialSource (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    canonicalDiscriminant (by simp) (periodOnePotential (continuousPotentialSource Φ)) z =
      classicalDiscriminant Φ z := by
  rw [canonicalDiscriminant_eq_l2_source]
  change l2Discriminant (sourcePhysicalL2 (sourcePhysicalL2Equiv.symm
    (continuousPotentialL2CLM Φ))) z = _
  rw [sourcePhysicalL2_equiv_symm,continuousPotentialL2CLM_apply,l2Discriminant_of_continuous]

theorem continuousPotentialSource_realType (Φ : Curve (ℂ × ℂ))
    (hΦ : ∀ t, (Φ t).2 = conj (Φ t).1) :
    continuousPotentialSource Φ ∈ realTypeSourceSubmodule 2 := by
  apply (sourcePhysicalL2_realType_iff _).mp
  change IsClassicalRealType (intervalL2Representative (sourcePhysicalL2
    (sourcePhysicalL2Equiv.symm (continuousPotentialL2CLM Φ))))
  rw [sourcePhysicalL2_equiv_symm,continuousPotentialL2CLM_apply]
  filter_upwards [continuousPotentialL2Class_representative Φ] with x hx
  rw [hx]
  exact hΦ _

end NLS.ZakharovShabat
