import NLS.Fourier.ExponentialFourierSynthesis
import NLS.Fourier.AbelBoundaryCoefficients

noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.Fourier

/-- Original Abel membership yields actual exponential coefficient decay with
rate 2a, because physical period-one frequencies use the original labels 2n. -/
theorem exists_exponential_bound_of_abel {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (c : ℤ → ℂ)
    (hc : Memℓp (fun n => (SpectralWeight.abel s a hs ha (2*n):ℂ)*c n) p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, ‖c n‖ ≤ M*Real.exp (-(2*a)*|(n:ℝ)|) := by
  let b : Coeff p := ⟨fun n => (SpectralWeight.abel s a hs ha (2*n):ℂ)*c n,hc⟩
  refine ⟨‖b‖,norm_nonneg _,fun n => ?_⟩
  have hw : SpectralWeight.abel s a hs ha (2*n) =
      (1+|((2*n:ℤ):ℝ)*Real.pi|)^s*Real.exp ((2*a)*|(n:ℝ)|) := by
    rw [SpectralWeight.abel_apply]
    congr 2
    simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    ring
  have hP : 1 ≤ (1+|((2*n:ℤ):ℝ)*Real.pi|)^s :=
    Real.one_le_rpow (by linarith [abs_nonneg (((2*n:ℤ):ℝ)*Real.pi)]) hs
  have hb := lp.norm_apply_le_norm (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) b n
  change ‖(SpectralWeight.abel s a hs ha (2*n):ℂ)*c n‖ ≤ ‖b‖ at hb
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos ((SpectralWeight.abel s a hs ha).positive (2*n)),hw] at hb
  have he : Real.exp ((2*a)*|(n:ℝ)|)*‖c n‖ ≤ ‖b‖ := by
    have h := mul_le_mul_of_nonneg_right hP
      (mul_nonneg (Real.exp_pos ((2*a)*|(n:ℝ)|)).le (norm_nonneg (c n)))
    have h' : Real.exp ((2*a)*|(n:ℝ)|)*‖c n‖ ≤
        (1+|((2*n:ℤ):ℝ)*Real.pi|)^s*Real.exp ((2*a)*|(n:ℝ)|)*‖c n‖ := by
      simpa only [one_mul,mul_assoc] using h
    exact h'.trans hb
  have h := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(2*a)*|(n:ℝ)|)).le
  have hid : Real.exp ((2*a)*|(n:ℝ)|)*‖c n‖*Real.exp (-(2*a)*|(n:ℝ)|) = ‖c n‖ := by
    rw [mul_right_comm,← Real.exp_add]
    simp only [show (2*a)*|(n:ℝ)|+ -(2*a)*|(n:ℝ)| = 0 by ring,Real.exp_zero,one_mul]
  rwa [hid] at h

/-- Every original Abel datum has a holomorphic period-one Fourier extension to
the corrected open strip of half-width a/pi. -/
theorem analyticOnNhd_abelFourierExtension {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (c : ℤ → ℂ)
    (hc : Memℓp (fun n => (SpectralWeight.abel s a hs ha (2*n):ℂ)*c n) p) :
    AnalyticOnNhd ℂ (periodOneComplexSynthesis c) {z : ℂ | |z.im| < a/Real.pi} := by
  obtain ⟨M,hM,hb⟩ := exists_exponential_bound_of_abel s a hs ha c hc
  have hw : (2*a)/(2*Real.pi) = a/Real.pi := by field_simp
  simpa only [hw] using analyticOnNhd_periodOneComplexSynthesis c M (2*a) hM hb

/-- The extension's actual interior Fourier integrals retain every raw shifted coefficient. -/
theorem periodOneCoefficient_abelFourierExtension {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (c : ℤ → ℂ)
    (hc : Memℓp (fun n => (SpectralWeight.abel s a hs ha (2*n):ℂ)*c n) p)
    (y : ℝ) (hy : |y| < a/Real.pi) (n : ℤ) :
    periodOneCoefficient (fun x : ℝ => periodOneComplexSynthesis c ((x:ℂ)+y*I)) n =
      complexHorizontalCoefficients c y n := by
  obtain ⟨M,hM,hb⟩ := exists_exponential_bound_of_abel s a hs ha c hc
  apply periodOneCoefficient_complexSynthesis_horizontal c M (2*a) hM hb y _ n
  have hw : (2*a)/(2*Real.pi) = a/Real.pi := by field_simp
  simpa only [hw] using hy

/-- At height zero, the actual integral sequence is exactly the input Abel data. -/
theorem periodOneCoefficient_abelFourierExtension_zero {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (s a : ℝ) (hs : 0 ≤ s) (ha : 0 < a) (c : ℤ → ℂ)
    (hc : Memℓp (fun n => (SpectralWeight.abel s a hs ha.le (2*n):ℂ)*c n) p)
    (n : ℤ) : periodOneCoefficient (fun x : ℝ => periodOneComplexSynthesis c x) n = c n := by
  simpa only [Complex.ofReal_zero,zero_mul,add_zero,complexHorizontalCoefficients,
    mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul] using
    periodOneCoefficient_abelFourierExtension s a hs ha.le c hc 0
      (by simpa only [abs_zero] using div_pos ha Real.pi_pos) n

end NLS.Fourier
