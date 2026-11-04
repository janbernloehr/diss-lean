import NLS.Dynamics.PhaseContinuityEstimate

/-! # A fixed phase gap prevents a common limit at a fixed time

This is distinct from the unbounded-frequency compact-time obstruction.
No convergence of the individual frequencies is required: their difference
alone controls separation of two phase values with the same amplitude.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.Dynamics

/-- The scalar identity is an instance of the existing phase-flow increment
identity, with a sequence supported at one coordinate. -/
theorem norm_exp_phase_sub (x y : ℝ) (a : ℂ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) * a - Complex.exp ((y : ℂ) * Complex.I) * a‖ =
      ‖Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) - 1‖ * ‖a‖ := by
  simpa only [Coeff.phaseFlow_apply, mul_one, lp.single_apply, Pi.single_eq_same] using
    Coeff.norm_phaseFlow_sub_apply (p := 2) (fun _ => 1) x y (lp.single 2 (0 : ℤ) a) 0

/-- When the relative phase tends to pi, the values have limiting distance
twice the nonzero amplitude and cannot converge to the same point. -/
theorem not_tendsto_same_limit_of_phase_gap {ι : Type*} {l : Filter ι} [NeBot l]
    (t : ℝ) (f g : ι → ℝ) (amp : ι → ℂ) (a : ℂ) (ha : a ≠ 0)
    (hamp : Tendsto amp l (𝓝 a))
    (hgap : Tendsto (fun j => t * (g j - f j)) l (𝓝 Real.pi)) (b : ℂ) :
    ¬ (Tendsto (fun j => Complex.exp (((-t * f j : ℝ) : ℂ) * Complex.I) * amp j) l (𝓝 b) ∧
      Tendsto (fun j => Complex.exp (((-t * g j : ℝ) : ℂ) * Complex.I) * amp j) l (𝓝 b)) := by
  have hangle : Tendsto (fun j => -t * g j - (-t * f j)) l (𝓝 (-Real.pi)) := by
    convert hgap.neg using 1
    funext j
    ring
  have he := (((Complex.continuous_ofReal.tendsto (-Real.pi)).comp hangle).mul_const
    Complex.I).cexp
  have hdist : Tendsto (fun j =>
      ‖Complex.exp (((-t * g j : ℝ) : ℂ) * Complex.I) * amp j -
        Complex.exp (((-t * f j : ℝ) : ℂ) * Complex.I) * amp j‖) l (𝓝 (2 * ‖a‖)) := by
    have h := (he.sub_const 1).norm.mul hamp.norm
    have hvalue : Complex.exp (((-Real.pi : ℝ) : ℂ) * Complex.I) = -1 := by
      rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    simpa only [norm_exp_phase_sub, hvalue, show ‖(-1 : ℂ) - 1‖ = 2 by norm_num,
      Function.comp_def] using! h
  rintro ⟨hf, hg⟩
  have hz := (hg.sub hf).norm
  simp only [sub_self, norm_zero] at hz
  have heq := tendsto_nhds_unique hdist hz
  exact ha (norm_eq_zero.mp (by linarith [norm_nonneg a]))

/-- The same obstruction with the physical positive Fourier exponent.
Swapping the frequency families and reversing the scalar time in the
proved negative-sign identity retains the same positive phase gap. -/
theorem not_tendsto_same_limit_of_positive_phase_gap {ι : Type*} {l : Filter ι} [NeBot l]
    (t : ℝ) (f g : ι → ℝ) (amp : ι → ℂ) (a : ℂ) (ha : a≠0)
    (hamp : Tendsto amp l (𝓝 a))
    (hgap : Tendsto (fun j => t*(g j-f j)) l (𝓝 Real.pi)) (b : ℂ) :
    ¬ (Tendsto (fun j => Complex.exp (((t*f j:ℝ):ℂ)*Complex.I)*amp j) l (𝓝 b) ∧
      Tendsto (fun j => Complex.exp (((t*g j:ℝ):ℂ)*Complex.I)*amp j) l (𝓝 b)) := by
  have hg : Tendsto (fun j => (-t)*(f j-g j)) l (𝓝 Real.pi) := by
    convert hgap using 1
    funext j
    ring
  have h := not_tendsto_same_limit_of_phase_gap (-t) g f amp a ha hamp hg b
  simpa only [neg_neg,and_comm] using h

end NLS.Dynamics
