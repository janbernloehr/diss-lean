import NLS.ZakharovShabat.ClassicalL2Stability
import NLS.ZakharovShabat.ClassicalHorizontalStripBounds

/-! Physical L2 stability uniform in the REAL frequency. The exact spectral
gauge removes the large real spectral part without changing any L2 distance. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Real spectral gauge preserves differences as ACTUAL continuous curves. -/
theorem realSpectralGauge_sub (phi psi : Curve (ℂ × ℂ)) (x : ℝ) :
    realSpectralGauge (phi-psi) x = realSpectralGauge phi x-realSpectralGauge psi x := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext <;> simp only [realSpectralGauge_apply,ContinuousMap.sub_apply,
    Prod.fst_sub,Prod.snd_sub] <;> ring

/-- The gauge preserves the exact physical Hilbert L2 potential budget. -/
theorem classicalPotentialL2Norm_realSpectralGauge (phi : Curve (ℂ × ℂ)) (x : ℝ) :
    classicalPotentialL2Norm (realSpectralGauge phi x) = classicalPotentialL2Norm phi := by
  unfold classicalPotentialL2Norm
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht
  have he : extend (realSpectralGauge phi x) t =
      (realSpectralPhase (2*x) t*(extend phi t).1,realSpectralPhase (-2*x) t*(extend phi t).2) := by
    simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ ht',realSpectralGauge_apply]
  dsimp only
  rw [he]
  simp only [norm_mul,norm_realSpectralPhase,one_mul]

/-- A common phase rotation preserves the EXACT difference of solutions. -/
theorem norm_classicalSolution_sub_real_shift (phi psi : Curve (ℂ × ℂ))
    (z : ℂ) (x : ℝ) (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    ‖classicalSolution phi z v t-classicalSolution psi z v t‖ =
      ‖classicalSolution (realSpectralGauge phi x) (z-x) v t-
        classicalSolution (realSpectralGauge psi x) (z-x) v t‖ := by
  rw [← classicalPhaseRotatedSolution_eq,← classicalPhaseRotatedSolution_eq]
  simp only [classicalPhaseRotatedSolution,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
    ← mul_sub,norm_mul,norm_realSpectralPhase,one_mul]

/-- The actual classical solution has a physical-L2 bound that depends
ONLY on imaginary height, uniformly over arbitrarily large real frequencies. -/
theorem norm_classicalSolution_le_exp_im_L2 (phi : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    ‖classicalSolution phi z v t‖ ≤ ‖v‖*Real.exp (|z.im|+classicalPotentialL2Norm phi) := by
  rw [norm_classicalSolution_real_shift phi z z.re v t]
  simpa only [norm_spectralParameter_sub_re,classicalPotentialL2Norm_realSpectralGauge] using
    norm_classicalSolution_le_exp_L2 (realSpectralGauge phi z.re) (z-z.re) v t

/-- Full physical L2 stability depends ONLY on the imaginary height,
with no real-frequency growth in its constant. -/
theorem norm_classicalSolution_sub_le_im_L2 (phi psi : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    ‖classicalSolution phi z v t-classicalSolution psi z v t‖ ≤
      ‖v‖*Real.exp (2*|z.im|+classicalPotentialL2Norm phi+classicalPotentialL2Norm psi)*
        classicalPotentialL2Norm (phi-psi) := by
  rw [norm_classicalSolution_sub_real_shift phi psi z z.re v t]
  simpa only [norm_spectralParameter_sub_re,← realSpectralGauge_sub,
    classicalPotentialL2Norm_realSpectralGauge] using
    norm_classicalSolution_sub_le_L2 (realSpectralGauge phi z.re) (realSpectralGauge psi z.re) (z-z.re) v t

end NLS.ZakharovShabat
