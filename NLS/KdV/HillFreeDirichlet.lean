import NLS.KdV.HillL2DirichletCharacteristic
import NLS.KdV.HillCanonicalFreeLabels

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ComplexConjugate ENNReal

namespace NLS.KdV

theorem classicalHillFlow_free_sine (z : ℂ) (hz : z≠0) (t : Icc (0 : ℝ) 1) :
    classicalHillFlow 0 (z^2) (0,1) t=(sin (z*t.val)/z,cos (z*t.val)) := by
  apply Eq.symm
  apply solution_unique (classicalHillCoefficientCurve 0 (z^2)) (0,1)
    (fun x : ℝ => (sin (z*x)/z,cos (z*x))) (by fun_prop) (by simp) _ t.property
  intro s _
  have harg : HasDerivAt (fun w : ℂ => z*w) z (s.val : ℂ) := by
    convert! (hasDerivAt_id (s.val : ℂ)).const_mul z using 1
    ring
  have hsin := (harg.csin.div_const z).comp_ofReal
  have hcos := harg.ccos.comp_ofReal
  have hh := hsin.prodMk hcos
  change HasDerivAt (fun x : ℝ => (sin (z*x)/z,cos (z*x)))
    (cos (z*s.val),(0-z^2)*(sin (z*s.val)/z)) s.val
  convert! hh using 1
  apply Prod.ext <;> dsimp <;> field_simp [hz]
  ring

theorem classicalHillFlow_free_zero (t : Icc (0 : ℝ) 1) :
    classicalHillFlow 0 0 (0,1) t=((t.val : ℂ),1) := by
  apply Eq.symm
  apply solution_unique (classicalHillCoefficientCurve 0 0) (0,1)
    (fun x : ℝ => ((x : ℂ),1)) (by fun_prop) (by simp) _ t.property
  intro s _
  simp only [classicalHillCoefficientCurve,ContinuousMap.coe_mk,ContinuousLinearMap.coe_restrictScalars',
    classicalHillCoefficient_apply,ContinuousMap.zero_apply,sub_self,zero_mul]
  convert! Complex.ofRealCLM.hasDerivAt.prodMk (hasDerivAt_const s.val (1 : ℂ)) using 1

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
