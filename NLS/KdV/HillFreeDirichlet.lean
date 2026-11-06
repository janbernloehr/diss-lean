import NLS.KdV.ClassicalHillFreeDirichlet
import NLS.KdV.HillL2DirichletCharacteristic
import NLS.KdV.HillCanonicalFreeLabels

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ComplexConjugate ENNReal

namespace NLS.KdV

theorem hillL2DirichletCharacteristic_free_sq (z : ℂ) (hz : z≠0) :
    hillL2DirichletCharacteristic 0 (z^2)=sin z/z := by
  have he : SpectralWeight.one.toCoeff (hillContinuousCoefficients (0 : C(AddCircle (2 : ℝ),ℂ)))=(0 : Coeff 2) := by
    ext k
    simpa only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply,Fourier.continuousFourierCLM_apply] using
      congrArg (fun f : Coeff 2 => f k) (map_zero Fourier.continuousFourierCLM)
  rw [← he,hillL2DirichletCharacteristic_eq_classical]
  have hQ : hillUnitPotentialCurve (0 : C(AddCircle (2 : ℝ),ℂ))=0 := by ext s; rfl
  rw [hQ,classicalHillFlow_free_sine z hz ⟨1,by norm_num⟩]
  simp

theorem hillL2DirichletCharacteristic_free_zero : hillL2DirichletCharacteristic 0 0=1 := by
  have he : SpectralWeight.one.toCoeff (hillContinuousCoefficients (0 : C(AddCircle (2 : ℝ),ℂ)))=(0 : Coeff 2) := by
    ext k
    simpa only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply,Fourier.continuousFourierCLM_apply] using
      congrArg (fun f : Coeff 2 => f k) (map_zero Fourier.continuousFourierCLM)
  rw [← he,hillL2DirichletCharacteristic_eq_classical]
  have hQ : hillUnitPotentialCurve (0 : C(AddCircle (2 : ℝ),ℂ))=0 := by ext s; rfl
  rw [hQ,classicalHillFlow_free_zero ⟨1,by norm_num⟩]
  norm_num

theorem hillL2DirichletCharacteristic_free_nat_root (n : ℕ) (hn : 1≤n) :
    hillL2DirichletCharacteristic 0 (((n : ℂ)*Real.pi)^2)=0 := by
  rw [hillL2DirichletCharacteristic_free_sq _ (by exact mul_ne_zero (by exact_mod_cast (show n≠0 by omega)) (by exact_mod_cast Real.pi_ne_zero))]
  rw [← ofReal_natCast,← ofReal_mul,← ofReal_sin,Real.sin_nat_mul_pi,ofReal_zero,zero_div]

end NLS.KdV
