import NLS.KdV.HillL2DirichletCharacteristic
import NLS.KdV.ClassicalHillDirichlet
import NLS.KdV.HillL2ConstantShift

/-! # The shared Dirichlet API uses the original physical characteristic

The existing characteristic already has the required position and derivative
normalization. Reusing it avoids two modules defining the same frequency family.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

def hillL2Dirichlet (q : Coeff 2) (lambda : ℂ) : ℂ := hillL2DirichletCharacteristic q lambda

theorem hillL2Dirichlet_eq_characteristic (q : Coeff 2) (lambda : ℂ) :
    hillL2Dirichlet q lambda = hillL2DirichletCharacteristic q lambda := rfl

theorem hillL2Dirichlet_sq (q : Coeff 2) (z : ℂ) :
    hillL2Dirichlet q (z^2) = hillL2FrequencyDirichlet q z :=
  hillL2DirichletCharacteristic_sq q z

theorem analyticOnNhd_hillL2Dirichlet_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2Dirichlet p.2 p.1) univ :=
  analyticOnNhd_hillL2DirichletCharacteristic_joint

theorem hillL2Dirichlet_eq_classical (Q : C(AddCircle (2 : ℝ),ℂ)) (lambda : ℂ) :
    hillL2Dirichlet (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) lambda =
      classicalHillDirichlet (hillUnitPotentialCurve Q) lambda :=
  hillL2DirichletCharacteristic_eq_classical Q lambda

/-- The exact free zero-energy normalization, with no spurious root at zero. -/
theorem hillL2Dirichlet_free_zero : hillL2Dirichlet 0 0 = 1 := by
  have hcoef : SpectralWeight.one.toCoeff (hillContinuousCoefficients 0) = (0:Coeff 2) := by
    ext k
    simp [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply,fourierCoeff]
  rw [← hcoef,hillL2Dirichlet_eq_classical]
  have hcurve : hillUnitPotentialCurve 0 = 0 := by ext t; rfl
  rw [hcurve,classicalHillDirichlet_free_zero]

/-- The actual L2 Dirichlet characteristic has the physical constant-shift law. -/
theorem hillL2Dirichlet_add_const (q : Coeff 2) (c lambda : ℂ) :
    hillL2Dirichlet (q+lp.single 2 0 c) (lambda+c) = hillL2Dirichlet q lambda := by
  have hc (mu : ℂ) : Continuous (fun a : Coeff 2 => hillL2Dirichlet a mu) := by
    have h : Continuous (fun r : ℂ × Coeff 2 => hillL2Dirichlet r.2 r.1) :=
      analyticOnNhd_hillL2Dirichlet_joint.continuous
    have hm : Continuous (fun a : Coeff 2 => (mu,a)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using h.comp hm
  have hcont (Q : C(AddCircle (2:ℝ),ℂ)) :
      hillL2Dirichlet (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)+lp.single 2 0 c)
        (lambda+c) = hillL2Dirichlet (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) lambda := by
    have hcoef (P : C(AddCircle (2:ℝ),ℂ)) :
        continuousFourierCLM P = SpectralWeight.one.toCoeff (hillContinuousCoefficients P) := by
      ext k
      rw [continuousFourierCLM_apply]
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
    rw [← hcoef,← continuousFourierCLM_const c,← map_add,hcoef,
      hillL2Dirichlet_eq_classical]
    rw [hcoef Q,hillL2Dirichlet_eq_classical]
    have hcurve : hillUnitPotentialCurve (Q+ContinuousMap.const _ c) =
        hillUnitPotentialCurve Q+ContinuousMap.const _ c := by ext t; rfl
    rw [hcurve,classicalHillDirichlet_add_const,add_sub_cancel_right]
  have hfinite (a : ℤ →₀ ℂ) :
      hillL2Dirichlet (Coeff.ofFinsupp (p := 2) a+lp.single 2 0 c) (lambda+c) =
        hillL2Dirichlet (Coeff.ofFinsupp (p := 2) a) lambda := by
    let Q := continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have hQ : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) = Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact fourierCoeff_continuousSynthesis _ k
    rw [← hQ]
    exact hcont Q
  exact congrFun ((Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer
    ((hc (lambda+c)).comp (continuous_id.add continuous_const)) (hc lambda) (funext hfinite)) q

end NLS.KdV
