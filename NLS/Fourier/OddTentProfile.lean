import NLS.Fourier.TentProfile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Reflected tent cancellation

An early tent minus its reflection near the end of the period has zero
mean. Positive imaginary spectral parameters give a strictly positive
upper interaction integral despite this Fourier cancellation.
-/
noncomputable section
open Complex MeasureTheory Set intervalIntegral
namespace NLS.Fourier

/-- A signed pair of tents related by reflection in the middle of the period. -/
def oddTentProfile (a b x : ℝ) : ℝ := tentProfile a b x - tentProfile (1-b) (1-a) x

@[fun_prop] theorem continuous_oddTentProfile (a b : ℝ) : Continuous (oddTentProfile a b) := by
  unfold oddTentProfile
  fun_prop

/-- Reflection reverses the two affine sides of a tent. -/
theorem tentProfile_reflect (a b x : ℝ) :
    tentProfile (1-b) (1-a) (1-x) = tentProfile a b x := by
  unfold tentProfile
  rw [show 1-x-(1-b) = b-x by ring, show 1-a-(1-x) = x-a by ring, min_comm]

theorem oddTentProfile_reflect (a b x : ℝ) : oddTentProfile a b (1-x) = -oddTentProfile a b x := by
  have h := tentProfile_reflect a b (1-x)
  simp only [sub_sub_cancel] at h
  rw [oddTentProfile,oddTentProfile,tentProfile_reflect,← h]
  ring

/-- Reflected tents cancel the constant Fourier mode exactly. -/
theorem integral_oddTentProfile_zero (a b : ℝ) :
    (∫ x in (0 : ℝ)..1, oddTentProfile a b x) = 0 := by
  have h := intervalIntegral.integral_comp_sub_left (fun x => oddTentProfile a b x)
    (a := (0 : ℝ)) (b := 1) 1
  simp only [sub_self,sub_zero,oddTentProfile_reflect,intervalIntegral.integral_neg] at h
  linarith

/-- The support stays away from the two endpoints by at least a. -/
theorem oddTentProfile_eq_zero_near_ends (a b : ℝ) (hab : a ≤ b) (hb : b ≤ 1/2)
    {x : ℝ} (hx : x ≤ a ∨ 1-a ≤ x) : oddTentProfile a b x = 0 := by
  rcases hx with hx | hx
  · rw [oddTentProfile, tentProfile_eq_zero_left a b hx,
      tentProfile_eq_zero_left (1-b) (1-a) (by linarith),sub_self]
  · rw [oddTentProfile, tentProfile_eq_zero_right a b (by linarith),
      tentProfile_eq_zero_right (1-b) (1-a) hx,sub_self]

/-- Reflection moves the kernel instead of changing the early tent. -/
theorem integral_oddTentProfile_mul (a b : ℝ) (K : ℝ → ℝ) (hK : Continuous K) :
    (∫ x in (0 : ℝ)..1, oddTentProfile a b x*K x) =
      ∫ x in (0 : ℝ)..1, tentProfile a b x*(K x-K (1-x)) := by
  have hc₁ : Continuous (fun x => tentProfile a b x*K x) := by fun_prop
  have hc₂ : Continuous (fun x => tentProfile (1-b) (1-a) x*K x) := by fun_prop
  have hc₃ : Continuous (fun x => tentProfile a b x*K (1-x)) := by fun_prop
  simp only [oddTentProfile,sub_mul,mul_sub]
  rw [intervalIntegral.integral_sub (hc₁.intervalIntegrable _ _) (hc₂.intervalIntegrable _ _),
    intervalIntegral.integral_sub (hc₁.intervalIntegrable _ _) (hc₃.intervalIntegrable _ _)]
  congr 1
  have h := intervalIntegral.integral_comp_sub_left (fun x => tentProfile (1-b) (1-a) x*K x)
    (a := (0 : ℝ)) (b := 1) 1
  simpa only [sub_self,sub_zero,tentProfile_reflect] using h.symm

/-- Fourier cancellation does not remove the exponentially weighted upper interaction. -/
theorem integral_oddTentProfile_mul_exp_pos (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1/2) (H : ℝ) (hH : 0 < H) :
    0 < ∫ x in (0 : ℝ)..1, oddTentProfile a b x*Real.exp (-2*H*x) := by
  rw [integral_oddTentProfile_mul a b _ (by fun_prop)]
  apply intervalIntegral.integral_pos (by norm_num)
  · apply Continuous.continuousOn
    fun_prop
  · intro x _
    by_cases hx : x ≤ b
    · apply mul_nonneg (tentProfile_nonneg a b x)
      apply sub_nonneg.mpr
      apply Real.exp_le_exp.mpr
      nlinarith
    · rw [tentProfile_eq_zero_right a b (le_of_not_ge hx),zero_mul]
  · refine ⟨(a+b)/2,⟨by linarith,by linarith⟩,?_⟩
    apply mul_pos (tentProfile_pos (by linarith) (by linarith))
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    nlinarith

/-- The original Fourier coefficient is the literal unit-interval integral. -/
theorem periodOneCoefficient_eq_wave_integral (f : ℝ → ℂ) (n : ℤ) :
    periodOneCoefficient f n = ∫ x in (0 : ℝ)..1, f x*wave (-(2*n)) x := by
  rw [periodOneCoefficient,fourierCoeffOn_one]
  unfold halfCoefficient
  rw [← mul_assoc]
  norm_num

/-- The signed profile's mean vanishes in the original coefficient convention. -/
theorem periodOneCoefficient_oddTentProfile_zero (a b : ℝ) :
    periodOneCoefficient (fun x => (oddTentProfile a b x : ℂ)) 0 = 0 := by
  rw [periodOneCoefficient_eq_wave_integral]
  simp only [mul_zero,neg_zero,wave,Int.cast_zero,zero_mul,mul_zero,exp_zero,mul_one,
    intervalIntegral.integral_ofReal,integral_oddTentProfile_zero,ofReal_zero]

/-- Complex kernels obey the same reflection identity. -/
theorem integral_oddTentProfile_mul_complex (a b : ℝ) (K : ℝ → ℂ) (hK : Continuous K) :
    (∫ x in (0 : ℝ)..1, (oddTentProfile a b x : ℂ)*K x) =
      ∫ x in (0 : ℝ)..1, (tentProfile a b x : ℂ)*(K x-K (1-x)) := by
  have hc₁ : Continuous (fun x => (tentProfile a b x : ℂ)*K x) := by fun_prop
  have hc₂ : Continuous (fun x => (tentProfile (1-b) (1-a) x : ℂ)*K x) := by fun_prop
  have hc₃ : Continuous (fun x => (tentProfile a b x : ℂ)*K (1-x)) := by fun_prop
  simp only [oddTentProfile,ofReal_sub,sub_mul,mul_sub]
  rw [intervalIntegral.integral_sub (hc₁.intervalIntegrable _ _) (hc₂.intervalIntegrable _ _),
    intervalIntegral.integral_sub (hc₁.intervalIntegrable _ _) (hc₃.intervalIntegrable _ _)]
  congr 1
  have h := intervalIntegral.integral_comp_sub_left (fun x => (tentProfile (1-b) (1-a) x : ℂ)*K x)
    (a := (0 : ℝ)) (b := 1) 1
  simpa only [sub_self,sub_zero,tentProfile_reflect] using h.symm

/-- Linear phase cancellation at every frequency and displacement. -/
theorem norm_wave_sub_one_le_frequency (n : ℤ) (x : ℝ) :
    ‖wave n x-1‖ ≤ Real.pi*|(n : ℝ)| *|x| := by
  have he : wave n x = exp (I*((Real.pi*n*x : ℝ) : ℂ)) := by
    unfold wave
    congr 1
    push_cast
    ring
  rw [he]
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := Real.pi*n*x))

/-- The reflected even wave differs by at most its doubled phase displacement from the endpoint. -/
theorem norm_even_wave_sub_reflect_le (n : ℤ) (x : ℝ) :
    ‖wave (-(2*n)) x-wave (-(2*n)) (1-x)‖ ≤ 4*Real.pi*|(n : ℝ)| *|x| := by
  have he : wave (-(2*n)) (1-x) = wave (2*n) x := by
    rw [sub_eq_add_neg,wave_add_argument,show -(2*n) = 2*(-n) by ring,wave_even_at_one,one_mul]
    unfold wave
    congr 1
    push_cast
    ring
  rw [he]
  have h₁ := norm_wave_sub_one_le_frequency (-(2*n)) x
  have h₂ := norm_wave_sub_one_le_frequency (2*n) x
  have h := norm_sub_le (wave (-(2*n)) x-1) (wave (2*n) x-1)
  simp only [sub_sub_sub_cancel_right] at h
  simp only [Int.cast_neg,Int.cast_mul,Int.cast_ofNat,abs_neg,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h₁ h₂
  linarith

/-- Low frequencies benefit from cancellation between the two ends of the period. -/
theorem norm_periodOneCoefficient_oddTentProfile_le_low (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (n : ℤ) :
    ‖periodOneCoefficient (fun x => (oddTentProfile a b x : ℂ)) n‖ ≤
      Real.pi*|(n : ℝ)| *b*(b-a)^2 := by
  rw [periodOneCoefficient_eq_wave_integral,
    integral_oddTentProfile_mul_complex a b _ (continuous_wave _)]
  have hc : Continuous (fun x => ‖(tentProfile a b x : ℂ)*
      (wave (-(2*n)) x-wave (-(2*n)) (1-x))‖) := by fun_prop
  have hg : Continuous (fun x => tentProfile a b x*(4*Real.pi*|(n : ℝ)| *b)) := by fun_prop
  calc
    _ ≤ ∫ x in (0 : ℝ)..1, ‖(tentProfile a b x : ℂ)*
        (wave (-(2*n)) x-wave (-(2*n)) (1-x))‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ x in (0 : ℝ)..1, tentProfile a b x*(4*Real.pi*|(n : ℝ)| *b) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hc.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
      intro x hx
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (tentProfile_nonneg a b x)]
      by_cases hxb : x ≤ b
      · apply mul_le_mul_of_nonneg_left _ (tentProfile_nonneg a b x)
        exact (norm_even_wave_sub_reflect_le n x).trans (by
          rw [abs_of_nonneg hx.1]
          exact mul_le_mul_of_nonneg_left hxb (by positivity))
      · rw [tentProfile_eq_zero_right a b (le_of_not_ge hxb),zero_mul,zero_mul]
    _ = _ := by
      rw [intervalIntegral.integral_mul_const,integral_tentProfile_unit a b ha hab hb]
      ring

/-- The signed coefficient is the difference of the two actual tent coefficients. -/
theorem periodOneCoefficient_oddTentProfile_eq_sub (a b : ℝ) (n : ℤ) :
    periodOneCoefficient (fun x => (oddTentProfile a b x : ℂ)) n =
      periodOneCoefficient (fun x => (tentProfile a b x : ℂ)) n -
      periodOneCoefficient (fun x => (tentProfile (1-b) (1-a) x : ℂ)) n := by
  simp only [periodOneCoefficient_eq_wave_integral,oddTentProfile,ofReal_sub,sub_mul]
  apply intervalIntegral.integral_sub
  · exact (by fun_prop : Continuous (fun x => (tentProfile a b x : ℂ)*wave (-(2*n)) x)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun x => (tentProfile (1-b) (1-a) x : ℂ)*wave (-(2*n)) x)).intervalIntegrable _ _

/-- High frequencies retain quadratic decay after reflection and subtraction. -/
theorem norm_periodOneCoefficient_oddTentProfile_mul_frequency_le (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (n : ℤ) :
    (2*Real.pi*|(n : ℝ)|)^2 * ‖periodOneCoefficient (fun x => (oddTentProfile a b x : ℂ)) n‖ ≤ 8 := by
  rw [periodOneCoefficient_oddTentProfile_eq_sub]
  have h₁ := norm_periodOneCoefficient_tentProfile_mul_frequency_le a b ha hab hb n
  have h₂ := norm_periodOneCoefficient_tentProfile_mul_frequency_le (1-b) (1-a)
    (by linarith) (by linarith) (by linarith) n
  calc
    _ ≤ (2*Real.pi*|(n : ℝ)|)^2 *
        (‖periodOneCoefficient (fun x => (tentProfile a b x : ℂ)) n‖ +
         ‖periodOneCoefficient (fun x => (tentProfile (1-b) (1-a) x : ℂ)) n‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (sq_nonneg _)
    _ ≤ 8 := by nlinarith

/-- A quantitative lower bound for every early signed tent, before summing dyadic scales. -/
theorem integral_oddTentProfile_mul_exp_lower (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (H : ℝ) (hH : 0 ≤ H) :
    (Real.exp (-2*H*b)-Real.exp (-2*H*(1-b)))*(b-a)^2/4 ≤
      ∫ x in (0 : ℝ)..1, oddTentProfile a b x*Real.exp (-2*H*x) := by
  rw [integral_oddTentProfile_mul a b _ (by fun_prop)]
  have hc : Continuous (fun x => tentProfile a b x*
      (Real.exp (-2*H*b)-Real.exp (-2*H*(1-b)))) := by fun_prop
  have hg : Continuous (fun x => tentProfile a b x*
      (Real.exp (-2*H*x)-Real.exp (-2*H*(1-x)))) := by fun_prop
  calc
    _ = ∫ x in (0 : ℝ)..1, tentProfile a b x*
        (Real.exp (-2*H*b)-Real.exp (-2*H*(1-b))) := by
      rw [intervalIntegral.integral_mul_const,integral_tentProfile_unit a b ha hab hb]
      ring
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hc.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
      intro x _
      by_cases hx : x ≤ b
      · apply mul_le_mul_of_nonneg_left _ (tentProfile_nonneg a b x)
        apply sub_le_sub
        · apply Real.exp_le_exp.mpr
          nlinarith
        · apply Real.exp_le_exp.mpr
          nlinarith
      · rw [tentProfile_eq_zero_right a b (le_of_not_ge hx),zero_mul,zero_mul]

end NLS.Fourier
