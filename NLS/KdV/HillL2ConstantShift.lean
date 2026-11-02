import NLS.KdV.HillL2EnergyDiscriminant
import NLS.KdV.ClassicalHillFlow

/-! # Exact constant-potential translation of the physical Hill trace

Adding a constant to the potential and to the energy leaves the scalar
state equation unchanged. Continuous Fourier density transfers this
identity to the actual L2 monodromy, including complex constants and
zero energy.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.LinearVolterra NLS.Fourier
namespace NLS.KdV

theorem classicalHillDiscriminant_add_const (q : Curve ℂ) (c lambda : ℂ) :
    classicalHillDiscriminant (q+ContinuousMap.const _ c) (lambda+c) =
      classicalHillDiscriminant q lambda := by
  have hcoef : classicalHillCoefficientCurve (q+ContinuousMap.const _ c) (lambda+c) =
      classicalHillCoefficientCurve q lambda := by
    apply ContinuousMap.ext
    intro t
    change (classicalHillCoefficient (q t+c) (lambda+c)).restrictScalars ℝ =
      (classicalHillCoefficient (q t) lambda).restrictScalars ℝ
    rw [show classicalHillCoefficient (q t+c) (lambda+c) = classicalHillCoefficient (q t) lambda by
      unfold classicalHillCoefficient
      rw [show q t+c-(lambda+c) = q t-lambda by ring]]
  rw [← classicalHillFlow_trace,← classicalHillFlow_trace q lambda]
  simp only [classicalHillFlow,hcoef]

theorem continuousFourierCLM_const (c : ℂ) :
    continuousFourierCLM (ContinuousMap.const (AddCircle (2 : ℝ)) c) = lp.single 2 0 c := by
  ext k
  rw [continuousFourierCLM_apply]
  change fourierCoeff (fun _ : AddCircle (2 : ℝ) => c) k = _
  rw [show (fun _ : AddCircle (2 : ℝ) => c) = (fun x => c*(fourier 0) x) by funext x; simp]
  rw [fourierCoeff.const_mul,fourierCoeff_fourier]
  by_cases hk : k = 0 <;> simp [lp.single_apply,hk]

private theorem hillL2Discriminant_add_const_continuous
    (Q : C(AddCircle (2 : ℝ),ℂ)) (c lambda : ℂ) :
    hillL2Discriminant (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)+lp.single 2 0 c)
      (lambda+c) = hillL2Discriminant (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) lambda := by
  have hc (P : C(AddCircle (2 : ℝ),ℂ)) :
      continuousFourierCLM P = SpectralWeight.one.toCoeff (hillContinuousCoefficients P) := by
    ext k
    rw [continuousFourierCLM_apply]
    simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
  have hsum : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)+lp.single 2 0 c =
      SpectralWeight.one.toCoeff (hillContinuousCoefficients (Q+ContinuousMap.const _ c)) := by
    rw [← hc,← hc,map_add,continuousFourierCLM_const]
  rw [hsum,hillL2Discriminant_eq_classical,hillL2Discriminant_eq_classical]
  have hcurve : hillUnitPotentialCurve (Q+ContinuousMap.const _ c) =
      hillUnitPotentialCurve Q+ContinuousMap.const _ c := by
    apply ContinuousMap.ext
    intro t
    rfl
  rw [hcurve]
  exact classicalHillDiscriminant_add_const _ _ _

/-- The actual L2 Hill trace has the exact physical constant-shift identity. -/
theorem hillL2Discriminant_add_const (q : Coeff 2) (c lambda : ℂ) :
    hillL2Discriminant (q+lp.single 2 0 c) (lambda+c) = hillL2Discriminant q lambda := by
  have hcont (mu : ℂ) : Continuous (fun a : Coeff 2 => hillL2Discriminant a mu) := by
    have hc : Continuous (fun p : ℂ × Coeff 2 => hillL2Discriminant p.2 p.1) :=
      analyticOnNhd_hillL2Discriminant_joint.continuous
    have hm : Continuous (fun a : Coeff 2 => (mu,a)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using hc.comp hm
  have hleft : Continuous (fun a : Coeff 2 =>
      hillL2Discriminant (a+lp.single 2 0 c) (lambda+c)) :=
    (hcont (lambda+c)).comp (continuous_id.add continuous_const)
  have hfinite (a : ℤ →₀ ℂ) :
      hillL2Discriminant (Coeff.ofFinsupp (p := 2) a+lp.single 2 0 c) (lambda+c) =
        hillL2Discriminant (Coeff.ofFinsupp (p := 2) a) lambda := by
    let Q := continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have hQ : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) = Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact fourierCoeff_continuousSynthesis _ k
    rw [← hQ]
    exact hillL2Discriminant_add_const_continuous Q c lambda
  have he := (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer hleft (hcont lambda)
    (funext hfinite)
  exact congrFun he q

end NLS.KdV
