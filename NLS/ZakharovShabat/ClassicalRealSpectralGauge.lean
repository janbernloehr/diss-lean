import NLS.ZakharovShabat.RealSpectralGauge

/-!
# Removing the real spectral part by a phase rotation

The exact change of variables shifts `z` to `z-x` and replaces the potential
by its norm-preserving real spectral gauge.
-/

noncomputable section
open Set Complex
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

def classicalPhaseRotatedSolution (φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) (v : ℂ × ℂ)
    (t : ℝ) : ℂ × ℂ :=
  (realSpectralPhase x t * (classicalSolution φ z v t).1,
   realSpectralPhase (-x) t * (classicalSolution φ z v t).2)

@[simp] theorem classicalPhaseRotatedSolution_zero (φ : Curve (ℂ × ℂ))
    (z : ℂ) (x : ℝ) (v : ℂ × ℂ) : classicalPhaseRotatedSolution φ z x v 0 = v := by
  simp [classicalPhaseRotatedSolution]

@[simp] theorem norm_classicalPhaseRotatedSolution (φ : Curve (ℂ × ℂ))
    (z : ℂ) (x : ℝ) (v : ℂ × ℂ) (t : ℝ) :
    ‖classicalPhaseRotatedSolution φ z x v t‖ = ‖classicalSolution φ z v t‖ := by
  simp only [classicalPhaseRotatedSolution, Prod.norm_def, norm_mul, norm_realSpectralPhase, one_mul]

theorem continuous_classicalPhaseRotatedSolution (φ : Curve (ℂ × ℂ))
    (z : ℂ) (x : ℝ) (v : ℂ × ℂ) : Continuous (classicalPhaseRotatedSolution φ z x v) := by
  have hu := continuous_classicalSolution φ z v
  unfold classicalPhaseRotatedSolution realSpectralPhase
  fun_prop

theorem hasDerivAt_classicalPhaseRotatedSolution (φ : Curve (ℂ × ℂ))
    (z : ℂ) (x : ℝ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalPhaseRotatedSolution φ z x v)
      (classicalODECoefficient (realSpectralGauge φ x t) (z-x)
        (classicalPhaseRotatedSolution φ z x v t)) t := by
  have hu := hasDerivAt_classicalSolution φ z v t
  have hd := ((hasDerivAt_realSpectralPhase x t).mul (HasFDerivAt.hasDerivAt hu.fst)).prodMk
    ((hasDerivAt_realSpectralPhase (-x) t).mul (HasFDerivAt.hasDerivAt hu.snd))
  have hp : realSpectralPhase (2*x) t * realSpectralPhase (-x) t = realSpectralPhase x t := by
    rw [realSpectralPhase_mul, show 2*x + -x = x by ring]
  have hm : realSpectralPhase (-2*x) t * realSpectralPhase x t = realSpectralPhase (-x) t := by
    rw [realSpectralPhase_mul, show -2*x + x = -x by ring]
  convert! hd using 1
  apply Prod.ext <;>
    simp only [classicalPhaseRotatedSolution, classicalODECoefficient_apply, realSpectralGauge_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul,
      Complex.ofReal_neg] <;> dsimp
  · linear_combination (I * (φ t).1 * (classicalSolution φ z v t).2) * hp
  · linear_combination (-I * (φ t).2 * (classicalSolution φ z v t).1) * hm

/-- The rotated solution is exactly the unique solution of the shifted system. -/
theorem classicalPhaseRotatedSolution_eq (φ : Curve (ℂ × ℂ))
    (z : ℂ) (x : ℝ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalPhaseRotatedSolution φ z x v t = classicalSolution (realSpectralGauge φ x) (z-x) v t := by
  exact classicalSolution_unique (realSpectralGauge φ x) (z-x) v
    (classicalPhaseRotatedSolution φ z x v)
    (continuous_classicalPhaseRotatedSolution φ z x v).continuousOn
    (classicalPhaseRotatedSolution_zero φ z x v)
    (fun s _ => hasDerivAt_classicalPhaseRotatedSolution φ z x v s) t.property

/-- A real shift of the parameter can be absorbed without changing the solution norm. -/
theorem norm_classicalSolution_real_shift (φ : Curve (ℂ × ℂ))
    (z : ℂ) (x : ℝ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    ‖classicalSolution φ z v t‖ = ‖classicalSolution (realSpectralGauge φ x) (z-x) v t‖ := by
  rw [← classicalPhaseRotatedSolution_eq, norm_classicalPhaseRotatedSolution]

end NLS.ZakharovShabat
