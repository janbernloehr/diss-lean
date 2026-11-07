import NLS.KdV.ClassicalHillTraceFamily
import NLS.KdV.HillL2SourcePrimitive
import NLS.KdV.ClassicalHillPrimitiveSheets

/-! # Exact continuous/physical L2 Hill primitive comparison

Functoriality identifies the actual free-normalized root and primitive,
not just their squares or exponentials. No new logarithm period or sheet
sign is selected when taking the continuous potential's Fourier coefficients.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier NLS.ComplexAnalysis
namespace NLS.KdV

theorem continuousFourierCLM_eq_hillContinuousCoefficients (Q : C(AddCircle (2 : ℝ), ℂ)) :
    continuousFourierCLM Q = SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) := by
  ext k
  simp only [continuousFourierCLM_apply, SpectralWeight.toCoeff_apply, hillContinuousCoefficients_apply]

def continuousHillTraceFamily : TracePrimitiveFamily C(AddCircle (2 : ℝ), ℂ) :=
  classicalHillTraceFamily.pullback hillUnitPotentialCurveCLM

theorem hillL2ContinuationDomain_continuous_iff (Q : C(AddCircle (2 : ℝ), ℂ)) (z : ℂ) :
    (z,continuousFourierCLM Q) ∈ hillL2ContinuationDomain ↔
      (z,hillUnitPotentialCurve Q) ∈ classicalHillContinuationDomain := by
  have h₁ := TracePrimitiveFamily.continuationDomain_comp_iff continuousHillTraceFamily
    hillL2SourceFamily continuousFourierCLM (fun w a => by
      change hillL2Discriminant (continuousFourierCLM a) w =
        classicalHillDiscriminant (hillUnitPotentialCurve a) w
      rw [continuousFourierCLM_eq_hillContinuousCoefficients,hillL2Discriminant_eq_classical]) rfl z Q
  have h₂ := TracePrimitiveFamily.continuationDomain_comp_iff continuousHillTraceFamily
    classicalHillTraceFamily hillUnitPotentialCurveCLM (fun _ _ => rfl) rfl z Q
  exact h₁.trans h₂.symm

theorem hillL2ContinuedPrimitive_eq_classical (Q : C(AddCircle (2 : ℝ), ℂ)) (z : ℂ)
    (ht : (z,hillUnitPotentialCurve Q) ∈ classicalHillContinuationDomain) :
    hillL2ContinuedPrimitive (z,continuousFourierCLM Q) =
      classicalHillContinuedPrimitive (z,hillUnitPotentialCurve Q) := by
  have h₂ : (z,Q) ∈ continuousHillTraceFamily.continuationDomain :=
    (TracePrimitiveFamily.continuationDomain_comp_iff continuousHillTraceFamily
      classicalHillTraceFamily hillUnitPotentialCurveCLM (fun _ _ => rfl) rfl z Q).mp ht
  have hL := TracePrimitiveFamily.primitive_comp continuousHillTraceFamily hillL2SourceFamily
    continuousFourierCLM (fun w a => by
      change hillL2Discriminant (continuousFourierCLM a) w =
        classicalHillDiscriminant (hillUnitPotentialCurve a) w
      rw [continuousFourierCLM_eq_hillContinuousCoefficients,hillL2Discriminant_eq_classical])
    (fun _ => rfl) rfl z Q h₂
  have hC := TracePrimitiveFamily.primitive_comp continuousHillTraceFamily classicalHillTraceFamily
    hillUnitPotentialCurveCLM (fun _ _ => rfl) (fun _ => rfl) rfl z Q h₂
  exact hL.trans hC.symm

theorem hillL2ContinuedPrimitive_re_sign_continuous (Q : C(AddCircle (2 : ℝ), ℂ))
    (hQ : ∀ t : Icc (0 : ℝ) 1, (hillUnitPotentialCurve Q t).im = 0)
    (z : ℂ) (hz : z.im ≠ 0) :
    0 < z.im*(hillL2ContinuedPrimitive (z,continuousFourierCLM Q)).re := by
  rw [hillL2ContinuedPrimitive_eq_classical Q z
    (mem_classicalHillContinuationDomain_of_im_ne_zero _ hQ z hz)]
  exact classicalHillContinuedPrimitive_re_sign _ hQ z hz

end NLS.KdV
