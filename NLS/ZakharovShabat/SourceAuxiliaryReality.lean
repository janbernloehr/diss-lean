import NLS.ZakharovShabat.SourceAuxiliarySpectra
import NLS.ZakharovShabat.AuxiliaryReality

/-!
# Reality of the original auxiliary spectra

The common completed Neumann potential reflection preserves real type.
Every spectral value of either actual original auxiliary restriction is real
for real-type input. This proves Proposition 5.2(iv), independently of the
printed numerical localization height.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAuxiliarySpectrum_im_eq_zero_of_realType (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann)
    (hr : IsRealType (CoeffPair.toMax p φ)) (z : ℂ)
    (hz : z ∈ sourceAuxiliarySpectrum b hp φ hφ) : z.im = 0 := by
  rw [sourceAuxiliarySpectrum_eq] at hz
  exact auxiliarySpectrum_im_eq_zero_of_realType b hp _ hφ hr z hz

theorem toMax_sourceAuxiliaryReflectedPotential (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    CoeffPair.toMax p (sourceAuxiliaryReflectedPotential hp1 hp φ) =
      (auxiliaryPeriodOnePotential hp hp1 φ).val := by
  apply Prod.ext <;> apply lp.ext <;> funext n
  · change (sourceBoundaryZeroWeightEquiv _).fst n = _
    rw [sourceBoundaryZeroWeightEquiv_fst, sourceIntervalExtensionToBoundary_fst]
    rfl
  · change (sourceBoundaryZeroWeightEquiv _).snd n = _
    rw [sourceBoundaryZeroWeightEquiv_snd, sourceIntervalExtensionToBoundary_snd]
    rfl

theorem isRealType_sourceAuxiliaryReflectedPotential (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hr : IsRealType (CoeffPair.toMax p φ)) :
    IsRealType (CoeffPair.toMax p (sourceAuxiliaryReflectedPotential hp1 hp φ)) := by
  rw [toMax_sourceAuxiliaryReflectedPotential]
  exact isRealType_auxiliaryPeriodOnePotential hp hp1 φ hr

theorem sourceAuxiliaryReflectedSpectrum_im_eq_zero_of_realType (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) (hr : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceAuxiliarySpectrum b hp (sourceAuxiliaryReflectedPotential hp1 hp φ)
      (sourceAuxiliaryReflectedPotential_mem hp1 hp φ)) : z.im = 0 :=
  sourceAuxiliarySpectrum_im_eq_zero_of_realType b hp _ _
    (isRealType_sourceAuxiliaryReflectedPotential hp1 hp φ hr) z hz

end NLS.ZakharovShabat
