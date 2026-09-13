import NLS.ZakharovShabat.ClassicalDuhamelBounds
import NLS.ComplexAnalysis.CoupledVolterraBounds

/-!
# Unconditional classical bounds at large imaginary height

The coupled Volterra estimate removes the opposite-coordinate hypothesis.
The threshold and constants depend only on the potential supremum norm and
the imaginary height, with no dependence on the real spectral parameter.
-/

noncomputable section
open Set Complex
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

private theorem norm_coupling_fst_le (φ : Curve (ℂ × ℂ)) (s : ℝ) :
    ‖I * (NLS.LinearVolterra.extend φ s).1‖ ≤ ‖φ‖ := by
  rw [norm_mul, Complex.norm_I, one_mul]
  exact (norm_fst_le _).trans (φ.norm_coe_le_norm _)

private theorem norm_coupling_snd_le (φ : Curve (ℂ × ℂ)) (s : ℝ) :
    ‖(-I) * (NLS.LinearVolterra.extend φ s).2‖ ≤ ‖φ‖ := by
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact (norm_snd_le _).trans (φ.norm_coe_le_norm _)

/-- Both upper-normalized coordinates have explicit bounds once the imaginary
height dominates the squared potential norm. -/
theorem classicalWeightedSolution_upper_bounds (φ : Curve (ℂ × ℂ))
    (z : ℂ) (hz : 0 < z.im) (hlarge : ‖φ‖^2 ≤ z.im) (v : ℂ × ℂ) :
    let K := 2 * (‖v.1‖ + ‖φ‖ * ‖v.2‖ / (2*z.im))
    ∀ t : Icc (0 : ℝ) 1,
      ‖(classicalWeightedSolution φ z (I*z) v t).1‖ ≤ K ∧
      ‖(classicalWeightedSolution φ z (I*z) v t).1 - v.1‖ ≤
        ‖φ‖ * (‖v.2‖/(2*z.im) + ‖φ‖*K/(2*z.im)) ∧
      ‖(classicalWeightedSolution φ z (I*z) v t).2 - exp ((2*I*z)*t.val)*v.2‖ ≤
        ‖φ‖*K/(2*z.im) := by
  have h := coupled_volterra_bounds
    (fun s => (classicalWeightedSolution φ z (I*z) v s).1)
    (fun s => (classicalWeightedSolution φ z (I*z) v s).2)
    (fun s => I * (NLS.LinearVolterra.extend φ s).1)
    (fun s => (-I) * (NLS.LinearVolterra.extend φ s).2)
    (2*I*z) (2*z.im) ‖φ‖
    (continuous_classicalWeightedSolution φ z (I*z) v).fst
    (by positivity) (norm_nonneg _) (by simp [Complex.mul_re]) (by linarith)
    (fun s _ => norm_coupling_fst_le φ s) (fun s _ => norm_coupling_snd_le φ s)
    (by intro t; simpa only [classicalWeightedSolution_zero] using
      classicalWeightedSolution_upper_fst φ z v t)
    (by intro t; simpa only [classicalWeightedSolution_zero] using
      classicalWeightedSolution_upper_snd φ z v t)
  simpa only [classicalWeightedSolution_zero] using h

/-- The lower-half-plane statement swaps the coordinates and retains positive
decay rate `-2 Im z`. -/
theorem classicalWeightedSolution_lower_bounds (φ : Curve (ℂ × ℂ))
    (z : ℂ) (hz : z.im < 0) (hlarge : ‖φ‖^2 ≤ -z.im) (v : ℂ × ℂ) :
    let K := 2 * (‖v.2‖ + ‖φ‖ * ‖v.1‖ / (-2*z.im))
    ∀ t : Icc (0 : ℝ) 1,
      ‖(classicalWeightedSolution φ z (-I*z) v t).2‖ ≤ K ∧
      ‖(classicalWeightedSolution φ z (-I*z) v t).2 - v.2‖ ≤
        ‖φ‖ * (‖v.1‖/(-2*z.im) + ‖φ‖*K/(-2*z.im)) ∧
      ‖(classicalWeightedSolution φ z (-I*z) v t).1 - exp ((-2*I*z)*t.val)*v.1‖ ≤
        ‖φ‖*K/(-2*z.im) := by
  have h := coupled_volterra_bounds
    (fun s => (classicalWeightedSolution φ z (-I*z) v s).2)
    (fun s => (classicalWeightedSolution φ z (-I*z) v s).1)
    (fun s => (-I) * (NLS.LinearVolterra.extend φ s).2)
    (fun s => I * (NLS.LinearVolterra.extend φ s).1)
    (-2*I*z) (-2*z.im) ‖φ‖
    (continuous_classicalWeightedSolution φ z (-I*z) v).snd
    (mul_pos_of_neg_of_neg (by norm_num) hz) (norm_nonneg _)
    (by simp [Complex.mul_re]) (by linarith)
    (fun s _ => norm_coupling_snd_le φ s) (fun s _ => norm_coupling_fst_le φ s)
    (by intro t; simpa only [classicalWeightedSolution_zero] using
      classicalWeightedSolution_lower_snd φ z v t)
    (by intro t; simpa only [classicalWeightedSolution_zero] using
      classicalWeightedSolution_lower_fst φ z v t)
  simpa only [classicalWeightedSolution_zero] using h

end NLS.ZakharovShabat
