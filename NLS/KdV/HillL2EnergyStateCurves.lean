import NLS.KdV.HillStateJointContinuity
import NLS.KdV.HillL2EnergyDiscriminant
import NLS.ComplexAnalysis.ContinuousEvenSquareDescent

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The genuine scalar state is even in frequency, including its
momentum component, at every complex rough coefficient source. -/
theorem hillL2FrequencyStateCurve_even (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ) :
    hillL2FrequencyStateCurve q (-z) v=hillL2FrequencyStateCurve q z v := by
  have hfinite (a : ℤ →₀ ℂ) : hillL2FrequencyStateCurve (Coeff.ofFinsupp (p := 2) a) (-z) v=
      hillL2FrequencyStateCurve (Coeff.ofFinsupp (p := 2) a) z v := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)=Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    apply ContinuousMap.ext
    intro t
    rw [← hq,hillL2FrequencyStateCurve_eq_classical,hillL2FrequencyStateCurve_eq_classical,neg_sq]
  have he : (fun a : Coeff 2 => hillL2FrequencyStateCurve a (-z) v)=
      (fun a : Coeff 2 => hillL2FrequencyStateCurve a z v) :=
    (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer
      (continuous_hillL2FrequencyStateCurve (-z) v) (continuous_hillL2FrequencyStateCurve z v) (funext hfinite)
  exact congrFun he q

theorem hillL2FrequencyStateCurve_eq_of_sq_eq
    (q : Coeff 2) (z w : ℂ) (v : ℂ × ℂ) (he : z^2=w^2) :
    hillL2FrequencyStateCurve q z v=hillL2FrequencyStateCurve q w v := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
  · rw [h]
  · rw [h,hillL2FrequencyStateCurve_even]

def hillL2EnergyStateCurve (q : Coeff 2) (energy : ℂ) (v : ℂ × ℂ) : Curve (ℂ × ℂ) :=
  hillL2FrequencyStateCurve q (Complex.sqrt energy) v

theorem hillL2EnergyStateCurve_eq_of_sq
    (q : Coeff 2) (energy z : ℂ) (v : ℂ × ℂ) (hz : z^2=energy) :
    hillL2EnergyStateCurve q energy v=hillL2FrequencyStateCurve q z v :=
  hillL2FrequencyStateCurve_eq_of_sq_eq q _ z v ((complex_sqrt_sq energy).trans hz.symm)

/-- The full actual scalar state descends jointly continuously to
energy and the rough source, including zero and the square-root cut. -/
theorem continuous_hillL2EnergyStateCurve_joint (v : ℂ × ℂ) :
    Continuous (fun p : ℂ × Coeff 2 => hillL2EnergyStateCurve p.2 p.1 v) :=
  continuous_even_square_descent (fun p : ℂ × Coeff 2 => hillL2FrequencyStateCurve p.2 p.1 v)
    (continuous_hillL2FrequencyStateCurve_joint v) (fun q z => hillL2FrequencyStateCurve_even q z v)
    Complex.sqrt complex_sqrt_sq

end NLS.KdV
