import NLS.ZakharovShabat.ClassicalRealSpectralGauge
import NLS.ZakharovShabat.ClassicalSolutionGrowth

/-!
# Classical growth controlled only by imaginary height

Real spectral gauge rotation preserves the potential and solution norms.
Gronwall therefore bounds the actual solution and trace independently of the
real spectral parameter, giving a uniform bound on every horizontal strip.
-/

noncomputable section
open Set Complex
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Removing the real spectral part leaves precisely the absolute imaginary height. -/
theorem norm_spectralParameter_sub_re (z : ℂ) : ‖z-(z.re : ℂ)‖ = |z.im| := by
  have he : z-(z.re : ℂ) = (z.im : ℂ)*I := by
    apply Complex.ext <;> simp
  rw [he, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The actual solution has exponential growth in the imaginary height only. -/
theorem norm_classicalSolution_le_exp_im (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    ‖classicalSolution φ z v t‖ ≤ ‖v‖ * Real.exp ((|z.im| + ‖φ‖) * t.val) := by
  rw [norm_classicalSolution_real_shift φ z z.re v t]
  simpa only [norm_spectralParameter_sub_re, norm_realSpectralGauge] using
    norm_classicalSolution_le_exp_norm (realSpectralGauge φ z.re) (z-z.re) v t

/-- A global trace estimate, uniform in the real spectral part. -/
theorem norm_classicalDiscriminant_le_exp_im (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    ‖classicalDiscriminant φ z‖ ≤ 2 * Real.exp (|z.im| + ‖φ‖) := by
  let t : Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
  have h₁ := norm_classicalSolution_le_exp_im φ z (1,0) t
  have h₂ := norm_classicalSolution_le_exp_im φ z (0,1) t
  have ht : ‖classicalDiscriminant φ z‖ ≤
      ‖classicalSolution φ z (1,0) 1‖ + ‖classicalSolution φ z (0,1) 1‖ := by
    simp only [classicalDiscriminant, classicalMonodromy, classicalFundamentalMatrix, Matrix.trace_fin_two_of]
    exact (norm_add_le _ _).trans (add_le_add (norm_fst_le _) (norm_snd_le _))
  apply ht.trans
  simpa [t, two_mul] using add_le_add h₁ h₂

/-- One explicit trace bound works for a whole norm ball of continuous potentials
and a whole horizontal spectral strip. -/
theorem norm_classicalDiscriminant_le_of_bounds (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (M H : ℝ) (hφ : ‖φ‖ ≤ M) (hz : |z.im| ≤ H) :
    ‖classicalDiscriminant φ z‖ ≤ 2 * Real.exp (H+M) :=
  (norm_classicalDiscriminant_le_exp_im φ z).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (add_le_add hz hφ)) (by norm_num))

/-- The classical discriminant maps every horizontal strip to a bounded set. -/
theorem isBounded_classicalDiscriminant_image_strip (φ : Curve (ℂ × ℂ)) (H : ℝ) :
    Bornology.IsBounded (classicalDiscriminant φ '' {z : ℂ | |z.im| ≤ H}) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨2 * Real.exp (H+‖φ‖), ?_⟩
  rintro w ⟨z, hz, rfl⟩
  exact norm_classicalDiscriminant_le_of_bounds φ z ‖φ‖ H le_rfl hz

end NLS.ZakharovShabat
