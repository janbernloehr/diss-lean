import NLS.KdV.ClassicalHillDiscAsymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # The actual high Hill trace stays in its parity half-plane

Uniform approximation on complete high discs fixes the half-plane of
the parity-normalized discriminant, also at branch points and along
all source paths of nearby complex potentials.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

private theorem real_part_cos (z : ℂ) : (cos z).re = Real.cos z.re * Real.cosh z.im := by
  rw [← re_add_im z,cos_add,cos_mul_I,sin_mul_I]
  simp only [← ofReal_cos,← ofReal_sin,← ofReal_cosh,← ofReal_sinh,
    sub_re,add_re,add_im,mul_re,mul_im,ofReal_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
    sub_zero,add_zero,zero_add,mul_one]

/-- The free cosine has a definite positive real part on the full
quarter-pi disc about zero. -/
theorem one_half_lt_re_cos_of_norm_le (z : ℂ) (hz : ‖z‖ ≤ Real.pi/4) :
    (1/2 : ℝ) < (cos z).re := by
  have hr : |z.re| < Real.pi/3 := ((abs_re_le_norm z).trans hz).trans_lt (by linarith [Real.pi_pos])
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg z.re)
    (by linarith [Real.pi_pos] : Real.pi/3 ≤ Real.pi) hr
  rw [Real.cos_pi_div_three,Real.cos_abs] at hc
  rw [real_part_cos]
  nlinarith [Real.one_le_cosh z.im]

/-- Exact free parity normalization in the frequency coordinate. -/
theorem freeHillTrace_parity_shift (n : ℕ) (z : ℂ) :
    (-1 : ℂ)^n*(2*cos z) = 2*cos (z-(Real.pi : ℂ)*n) := by
  have hs : sin ((Real.pi : ℂ)*n) = 0 := by
    simpa only [mul_comm] using Complex.sin_nat_mul_pi n
  have hc : cos ((Real.pi : ℂ)*n) = (-1 : ℂ)^n := by
    have h := congrArg Complex.ofReal (Real.cos_nat_mul_pi n)
    simpa only [ofReal_cos,ofReal_mul,ofReal_natCast,ofReal_pow,ofReal_neg,ofReal_one,mul_comm] using h
  rw [cos_sub,hs,hc,mul_zero,add_zero]
  ring

/-- A small additive trace error fixes the correct parity half-plane
on every point of a high disc, including its interior spectral zeros. -/
theorem classicalHillTrace_parity_re_pos_of_error
    (q : Curve ℂ) (n : ℕ) (z : ℂ)
    (hz : z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4))
    (he : ‖classicalHillDiscriminant q (z^2)-2*cos z‖ ≤ (1/2 : ℝ)) :
    0 < ((-1 : ℂ)^n*classicalHillDiscriminant q (z^2)).re := by
  have hf := one_half_lt_re_cos_of_norm_le (z-(Real.pi : ℂ)*n)
    (by simpa only [mem_closedBall,dist_eq_norm] using hz)
  have hd : ‖(-1 : ℂ)^n*classicalHillDiscriminant q (z^2)-(-1 : ℂ)^n*(2*cos z)‖ ≤ (1/2 : ℝ) := by
    rw [← mul_sub,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    exact he
  have hdiff := abs_le.mp ((abs_re_le_norm _).trans hd)
  rw [freeHillTrace_parity_shift,sub_re] at hdiff
  have htwo : (2*cos (z-(Real.pi : ℂ)*n)).re = 2*(cos (z-(Real.pi : ℂ)*n)).re := by simp
  rw [htwo] at hdiff
  linarith [hdiff.1]

/-- One common complex neighborhood has the correct parity trace
half-plane on every complete high disc and every straight source path. -/
theorem exists_classicalHill_source_high_trace_phase (q : Curve ℂ) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ s ∈ Icc (0 : ℝ) 1, ∀ n : ℕ, N ≤ n →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4),
          0 < ((-1 : ℂ)^n*classicalHillDiscriminant ((s : ℂ) • a) (z^2)).re := by
  obtain ⟨N,V,hN,hV,hq,hd⟩ := exists_classicalHill_source_disc_trace_approximation q
    (Real.pi/4) (by positivity) le_rfl (1/2) (by norm_num)
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro a ha s hs n hn z hz
  apply classicalHillTrace_parity_re_pos_of_error _ n z hz
  exact hd a ha s hs n (by simpa only [Int.natAbs_natCast] using hn) z
    (by simpa only [Int.cast_natCast] using hz)

end NLS.KdV
