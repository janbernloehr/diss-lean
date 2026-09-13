import NLS.ZakharovShabat.ClassicalDuhamel
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Unit-modulus real spectral phases

Opposite phases rotate the potential without changing its supremum norm.
-/

noncomputable section
open Set Complex
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

def realSpectralPhase (x t : ℝ) : ℂ := exp (I*x*t)

@[simp] theorem realSpectralPhase_zero_time (x : ℝ) : realSpectralPhase x 0 = 1 := by
  simp [realSpectralPhase]

@[simp] theorem realSpectralPhase_zero_parameter (t : ℝ) : realSpectralPhase 0 t = 1 := by
  simp [realSpectralPhase]

@[simp] theorem norm_realSpectralPhase (x t : ℝ) : ‖realSpectralPhase x t‖ = 1 := by
  simp [realSpectralPhase, Complex.norm_exp, Complex.mul_re]

theorem realSpectralPhase_mul (x y t : ℝ) :
    realSpectralPhase x t * realSpectralPhase y t = realSpectralPhase (x+y) t := by
  simp only [realSpectralPhase, ← exp_add]
  congr 1
  push_cast
  ring

theorem hasDerivAt_realSpectralPhase (x t : ℝ) :
    HasDerivAt (realSpectralPhase x) (realSpectralPhase x t * (I*x)) t :=
  hasDerivAt_complex_exp_mul (I*x) t

/-- Rotate the two potential coordinates by opposite phases at twice the frequency. -/
def realSpectralGauge (φ : Curve (ℂ × ℂ)) (x : ℝ) : Curve (ℂ × ℂ) where
  toFun t := (realSpectralPhase (2*x) t * (φ t).1, realSpectralPhase (-2*x) t * (φ t).2)
  continuous_toFun := by unfold realSpectralPhase; fun_prop

@[simp] theorem realSpectralGauge_apply (φ : Curve (ℂ × ℂ)) (x : ℝ) (t : Icc (0 : ℝ) 1) :
    realSpectralGauge φ x t =
      (realSpectralPhase (2*x) t * (φ t).1, realSpectralPhase (-2*x) t * (φ t).2) := rfl

@[simp] theorem norm_realSpectralGauge_apply (φ : Curve (ℂ × ℂ)) (x : ℝ) (t : Icc (0 : ℝ) 1) :
    ‖realSpectralGauge φ x t‖ = ‖φ t‖ := by
  simp only [realSpectralGauge_apply, Prod.norm_def, norm_mul, norm_realSpectralPhase, one_mul]

@[simp] theorem norm_realSpectralGauge (φ : Curve (ℂ × ℂ)) (x : ℝ) :
    ‖realSpectralGauge φ x‖ = ‖φ‖ := by
  simp only [ContinuousMap.norm_eq_iSup_norm, norm_realSpectralGauge_apply]

@[simp] theorem realSpectralGauge_zero (φ : Curve (ℂ × ℂ)) : realSpectralGauge φ 0 = φ := by
  apply ContinuousMap.ext
  intro t
  simp only [realSpectralGauge_apply, mul_zero, realSpectralPhase_zero_parameter, one_mul]

end NLS.ZakharovShabat
