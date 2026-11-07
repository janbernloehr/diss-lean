import NLS.KdV.ClassicalHillFourierVariation
import NLS.ComplexAnalysis.SquarePullbackDerivative

/-! The free Dirichlet zeros are simple in the ORIGINAL energy variable.
The computation differentiates the actual entire scalar characteristic,
using its square-frequency pullback; it never differentiates a square root. -/
noncomputable section
open scoped Real Topology
open Set Complex Filter NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

theorem hillL2Dirichlet_zero_eq_classical (μ : ℂ) :
    hillL2Dirichlet 0 μ = classicalHillDirichlet 0 μ := by
  have hc : SpectralWeight.one.toCoeff (hillContinuousCoefficients (0 : C(AddCircle (2:ℝ),ℂ))) = 0 := by
    ext k
    simp [hillContinuousCoefficients_apply,fourierCoeff]
  have hcurve : hillUnitPotentialCurve (0 : C(AddCircle (2:ℝ),ℂ)) = 0 := by ext t; rfl
  rw [← hc,hillL2Dirichlet_eq_classical,hcurve]

theorem analyticOnNhd_classicalHillDirichlet_free :
    AnalyticOnNhd ℂ (classicalHillDirichlet 0) univ := by
  intro μ _
  have he : classicalHillDirichlet 0 = hillL2Dirichlet 0 :=
    funext (fun w => (hillL2Dirichlet_zero_eq_classical w).symm)
  rw [he]
  exact (analyticOnNhd_hillL2Dirichlet_joint (μ,0) (mem_univ _)).comp
    (f := fun w : ℂ => (w,(0 : Coeff 2))) (analyticAt_id.prod analyticAt_const)

theorem deriv_classicalHillDirichlet_free_sq (z : ℂ) (hz : z ≠ 0) :
    deriv (classicalHillDirichlet 0) (z^2) = (cos z*z-sin z)/(2*z^3) := by
  have hf := (analyticOnNhd_classicalHillDirichlet_free (z^2) (mem_univ _)).differentiableAt
  have hg : HasDerivAt (fun w : ℂ => sin w/w) ((cos z*z-sin z)/(z^2)) z := by
    simpa using! (Complex.hasDerivAt_sin z).div (hasDerivAt_id z) hz
  have he : (fun w => classicalHillDirichlet 0 (w^2)) =ᶠ[𝓝 z] fun w => sin w/w := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact classicalHillDirichlet_free_sq w hw
  rw [NLS.ComplexAnalysis.deriv_eq_of_square_pullback _ _ z _ hz hf hg he]
  field_simp [hz]

theorem hasDerivAt_classicalHillDirichlet_free_eigenvalue (n : ℕ+) :
    HasDerivAt (classicalHillDirichlet 0) ((-1:ℂ)^(n:ℕ)/(2*(π*n)^2)) ((π*n)^2) := by
  have hz : (π:ℂ)*n ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    (by exact_mod_cast n.ne_zero)
  have hd := (analyticOnNhd_classicalHillDirichlet_free ((π*n)^2) (mem_univ _)).differentiableAt.hasDerivAt
  rw [deriv_classicalHillDirichlet_free_sq (π*n) hz,complex_cos_nat_pi,complex_sin_nat_pi] at hd
  have hv : (-1:ℂ)^(n:ℕ)*(π*n)/(2*(π*n)^3) =
      (-1:ℂ)^(n:ℕ)/(2*(π*n)^2) := by
    field_simp [hz]
  simpa only [sub_zero,hv] using hd

theorem deriv_classicalHillDirichlet_free_eigenvalue_ne_zero (n : ℕ+) :
    deriv (classicalHillDirichlet 0) ((π*n)^2) ≠ 0 := by
  rw [(hasDerivAt_classicalHillDirichlet_free_eigenvalue n).deriv]
  exact div_ne_zero (pow_ne_zero _ (by norm_num))
    (mul_ne_zero (by norm_num) (pow_ne_zero _
      (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))))


theorem hillL2DirichletTerminal_zero_eq_classical (μ : ℂ) :
    hillL2DirichletTerminal 0 μ = classicalHillDirichletTerminal 0 μ := by
  have hc : SpectralWeight.one.toCoeff (hillContinuousCoefficients (0 : C(AddCircle (2:ℝ),ℂ))) = 0 := by
    ext k
    simp [hillContinuousCoefficients_apply,fourierCoeff]
  have hcurve : hillUnitPotentialCurve (0 : C(AddCircle (2:ℝ),ℂ)) = 0 := by ext t; rfl
  rw [← hc,hillL2DirichletTerminal_eq_classical,hcurve]

theorem analyticOnNhd_classicalHillDirichletTerminal_free :
    AnalyticOnNhd ℂ (classicalHillDirichletTerminal 0) univ := by
  intro μ _
  have he : classicalHillDirichletTerminal 0 = hillL2DirichletTerminal 0 :=
    funext (fun w => (hillL2DirichletTerminal_zero_eq_classical w).symm)
  rw [he]
  exact (analyticOnNhd_hillL2DirichletTerminal_joint (μ,0) (mem_univ _)).comp
    (f := fun w : ℂ => (w,(0 : Coeff 2))) (analyticAt_id.prod analyticAt_const)

theorem deriv_classicalHillDirichletTerminal_free_sq (z : ℂ) (hz : z ≠ 0) :
    deriv (classicalHillDirichletTerminal 0) (z^2) = -sin z/(2*z) := by
  have hf := (analyticOnNhd_classicalHillDirichletTerminal_free (z^2) (mem_univ _)).differentiableAt
  have he : (fun w => classicalHillDirichletTerminal 0 (w^2)) =ᶠ[𝓝 z] cos := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact classicalHillDirichletTerminal_free_sq w hw
  exact NLS.ComplexAnalysis.deriv_eq_of_square_pullback _ _ z _ hz hf
    (Complex.hasDerivAt_cos z) he

theorem hasDerivAt_classicalHillDirichletTerminal_free_eigenvalue (n : ℕ+) :
    HasDerivAt (classicalHillDirichletTerminal 0) 0 ((π*n)^2) := by
  have hz : (π:ℂ)*n ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    (by exact_mod_cast n.ne_zero)
  have hd := (analyticOnNhd_classicalHillDirichletTerminal_free ((π*n)^2) (mem_univ _)).differentiableAt.hasDerivAt
  simpa only [deriv_classicalHillDirichletTerminal_free_sq (π*n) hz,
    complex_sin_nat_pi,neg_zero,zero_div] using hd

end NLS.KdV
