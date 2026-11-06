import NLS.KdV.HillL2EnergyStateCurves
import NLS.KdV.HillDirichletSlopeShift

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Constant-potential translation preserves the full actual scalar energy-state curve. -/
theorem hillL2EnergyStateCurve_constant_shift (q : Coeff 2) (a c : ℂ) (v : ℂ × ℂ) :
    hillL2EnergyStateCurve (q+lp.single 2 0 c) (a+c) v=hillL2EnergyStateCurve q a v := by
  have hc (e : ℂ) : Continuous (fun p : Coeff 2 => hillL2EnergyStateCurve p e v) :=
    Continuous.comp (f := fun p : Coeff 2 => (e,p)) (continuous_hillL2EnergyStateCurve_joint v)
      (continuous_const.prodMk continuous_id)
  have hfinite (f : ℤ →₀ ℂ) :
      hillL2EnergyStateCurve (Coeff.ofFinsupp (p := 2) f+lp.single 2 0 c) (a+c) v=
        hillL2EnergyStateCurve (Coeff.ofFinsupp (p := 2) f) a v := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) f)
    let R := Q+ContinuousMap.const (AddCircle (2 : ℝ)) c
    have hQ : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)=Coeff.ofFinsupp (p := 2) f := by
      ext k
      rw [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    have hR : SpectralWeight.one.toCoeff (hillContinuousCoefficients R)=Coeff.ofFinsupp (p := 2) f+lp.single 2 0 c := by
      rw [toCoeff_hillContinuousCoefficients]
      dsimp only [R]
      rw [map_add,Fourier.continuousFourierCLM_const,←toCoeff_hillContinuousCoefficients,hQ]
    have he : hillUnitPotentialCurve R=hillUnitPotentialCurve Q+ContinuousMap.const _ c := by
      ext t
      rfl
    unfold hillL2EnergyStateCurve
    apply ContinuousMap.ext
    intro t
    rw [←hR,←hQ,hillL2FrequencyStateCurve_eq_classical,hillL2FrequencyStateCurve_eq_classical,
      complex_sqrt_sq,complex_sqrt_sq,he,classicalHillFlow_constant_shift]
  have heq := (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer
    ((hc (a+c)).comp (continuous_id.add continuous_const)) (hc a) (funext hfinite)
  exact congrFun heq q

end NLS.KdV
