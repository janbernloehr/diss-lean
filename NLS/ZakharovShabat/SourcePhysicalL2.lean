import NLS.ZakharovShabat.ContinuousSourceBoundaryRealization
import NLS.ZakharovShabat.ContinuousPotentialL2Class

/-! # The original source-to-physical L2 map

Reuse the established bounded restriction of Fourier synthesis and the
period-one source embedding. The map recovers continuous representatives
exactly and is available on every Hilbert source without extra hypotheses.
-/
noncomputable section
open Set MeasureTheory
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Any compatible continuous representative gives exactly the same original L2 class. -/
theorem physicalRestrictionL2_of_continuous (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] extend Φ) :
    physicalRestrictionL2 φ = continuousPotentialL2Class Φ :=
  intervalL2Representative_injective _ _ ((physicalRestrictionL2_representative φ).trans
    (hΦ.trans (continuousPotentialL2Class_representative Φ).symm))

/-- The original source-to-physical L2 map uses the established period-one Fourier embedding. -/
def sourcePhysicalL2 : CoeffPair 2 →L[ℂ] IntervalPairL2 := physicalRestrictionL2CLM.comp periodOnePotential

@[simp] theorem sourcePhysicalL2_apply (φ : CoeffPair 2) :
    sourcePhysicalL2 φ = physicalRestrictionL2 (periodOnePotential φ) := rfl

theorem sourcePhysicalL2_representative (φ : CoeffPair 2) :
    intervalL2Representative (sourcePhysicalL2 φ) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      physicalBase (periodOnePotential φ) := physicalRestrictionL2_representative _

theorem norm_sourcePhysicalL2_le (φ : CoeffPair 2) : ‖sourcePhysicalL2 φ‖ ≤ 2*‖φ‖ :=
  (norm_physicalRestrictionL2_le _).trans (mul_le_mul_of_nonneg_left (norm_periodOnePotential_le φ) (by norm_num))

/-- Exact physical recovery on the dense finite Fourier source subspace. -/
theorem sourcePhysicalL2_ofFinsupp (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    sourcePhysicalL2 (CoeffPair.ofFinsupp (p := 2) a) = continuousPotentialL2Class (finiteSourceCurve a) :=
  physicalRestrictionL2_of_continuous _ _ (finiteSource_physical_compatibility a).1

end NLS.ZakharovShabat
