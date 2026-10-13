import NLS.ZakharovShabat.SourceAuxiliaryExtension
import NLS.ZakharovShabat.SourceAuxiliaryBoundaryFourier
import NLS.ZakharovShabat.SourceLemma4_3Physical
import NLS.ZakharovShabat.AuxiliarySourceExtension

/-!
# Completed auxiliary extension on arbitrary physical L² input

The completed original-norm auxiliary extension has exactly the Fourier
coefficients of the physical phase-twisted reflection for arbitrary L² data.
For original auxiliary H¹ input it gives the same Sobolev extension as
Lemma 5.1. No endpoint matching is imposed on arbitrary L² input.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The completed original auxiliary map equals physical reflection on arbitrary L² input. -/
theorem auxiliarySourceExtension_two_ofFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    auxiliarySourceExtension b (by norm_num) (by simp) (sourceUnitIntervalL2Coefficients f hf) =
      sourceAuxiliaryIntervalExtensionCoefficients b f hf := by
  apply (CoeffPair.toMax 2).injective
  rw [toMax_auxiliarySourceExtension]
  apply Prod.ext <;> apply lp.ext <;> funext n
  · rw [auxiliaryIntervalExtensionCLM_fst]
    change halfIntervalCoeffs (by norm_num) (by simp)
      (unitIntervalMemLpCoefficients (fun x => (f x).1) hf.fst) n -
      Complex.I * extensionSign b * halfIntervalCoeffs (by norm_num) (by simp)
        (unitIntervalMemLpCoefficients (fun x => (f x).2) hf.snd) (-n) =
      (sourceAuxiliaryIntervalExtensionCoefficients b f hf).fst n
    rw [halfIntervalCoeffs_two_ofFunction, halfIntervalCoeffs_two_ofFunction]
    exact (sourceAuxiliaryIntervalExtensionCoefficients_raw b f hf n).1.symm
  · rw [auxiliaryIntervalExtensionCLM_snd]
    change halfIntervalCoeffs (by norm_num) (by simp)
      (unitIntervalMemLpCoefficients (fun x => (f x).2) hf.snd) n +
      Complex.I * extensionSign b * halfIntervalCoeffs (by norm_num) (by simp)
        (unitIntervalMemLpCoefficients (fun x => (f x).1) hf.fst) (-n) =
      (sourceAuxiliaryIntervalExtensionCoefficients b f hf).snd n
    rw [halfIntervalCoeffs_two_ofFunction, halfIntervalCoeffs_two_ofFunction]
    exact (sourceAuxiliaryIntervalExtensionCoefficients_raw b f hf n).2.symm

/-- The bounded source map reconstructs the actual auxiliary reflected function. -/
theorem auxiliarySourceExtension_two_physical (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    sourceCircleRepresentative (sourceCircleSynthesis
      (auxiliarySourceExtension b (by norm_num) (by simp) (sourceUnitIntervalL2Coefficients f hf)))
      =ᵐ[volume.restrict (Ioc 0 2)] auxiliaryIntervalExtension b f := by
  rw [auxiliarySourceExtension_two_ofFunction]
  exact sourceCircleSynthesis_auxiliaryIntervalExtension b f hf

/-- For original auxiliary-domain data, the completed map gives the same Sobolev extension. -/
theorem auxiliarySourceExtension_two_classical (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) (hL : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    auxiliarySourceExtension b (by norm_num) (by simp) (sourceUnitIntervalL2Coefficients f hL) =
      sourceDomainInclusion (sourceClassicalAuxiliaryExtension b f hf) := by
  rw [auxiliarySourceExtension_two_ofFunction, sourceAuxiliaryIntervalExtensionCoefficients_eq_classical b f hf hL]


/-- The original weighted-zero auxiliary target has the actual physical reflected coefficients. -/
theorem sourceAuxiliaryExtensionToBoundary_two_ofFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    sourceBoundaryZeroWeightEquiv
      (sourceAuxiliaryExtensionToBoundary b (by norm_num) (by simp) (sourceUnitIntervalL2Coefficients f hf)).val =
      sourceAuxiliaryIntervalExtensionCoefficients b f hf := by
  rw [sourceAuxiliaryExtensionToBoundary_eq_completed, auxiliarySourceExtension_two_ofFunction]

/-- Synthesis of the actual original target reconstructs the physical auxiliary reflection. -/
theorem sourceAuxiliaryExtensionToBoundary_two_physical (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    sourceCircleRepresentative (sourceCircleSynthesis (sourceBoundaryZeroWeightEquiv
      (sourceAuxiliaryExtensionToBoundary b (by norm_num) (by simp) (sourceUnitIntervalL2Coefficients f hf)).val))
      =ᵐ[volume.restrict (Ioc 0 2)] auxiliaryIntervalExtension b f := by
  rw [sourceAuxiliaryExtensionToBoundary_two_ofFunction]
  exact sourceCircleSynthesis_auxiliaryIntervalExtension b f hf

end NLS.ZakharovShabat
