import NLS.Fourier.ContinuousPeriodOneRealization

/-! # Continuous compactly supported tent profiles

These profiles supply ordered couplings with explicit support. Their
exponential integrals retain the exact second-difference formula, which
will be used for both Fourier coefficients and interaction integrals.
-/
noncomputable section
open Complex MeasureTheory Set intervalIntegral
namespace NLS.Fourier

/-- The tent with slopes one and minus one on `[a,b]`, zero outside. -/
def tentProfile (a b x : ℝ) : ℝ := max 0 (min (x-a) (b-x))

@[fun_prop] theorem continuous_tentProfile (a b : ℝ) : Continuous (tentProfile a b) := by
  unfold tentProfile
  fun_prop

theorem tentProfile_nonneg (a b x : ℝ) : 0 ≤ tentProfile a b x := le_max_left _ _

theorem tentProfile_eq_zero_left (a b : ℝ) {x : ℝ} (hx : x ≤ a) : tentProfile a b x = 0 := by
  unfold tentProfile
  exact max_eq_left ((min_le_left _ _).trans (sub_nonpos.mpr hx))

theorem tentProfile_eq_zero_right (a b : ℝ) {x : ℝ} (hx : b ≤ x) : tentProfile a b x = 0 := by
  unfold tentProfile
  exact max_eq_left ((min_le_right _ _).trans (sub_nonpos.mpr hx))

theorem tentProfile_pos {a b x : ℝ} (ha : a < x) (hb : x < b) : 0 < tentProfile a b x := by
  exact lt_max_of_lt_right (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb))

theorem tentProfile_left {a b x : ℝ} (ha : a ≤ x) (hm : x ≤ (a+b)/2) :
    tentProfile a b x = x-a := by
  rw [tentProfile, min_eq_left (by linarith), max_eq_right (sub_nonneg.mpr ha)]

theorem tentProfile_right {a b x : ℝ} (hm : (a+b)/2 ≤ x) (hb : x ≤ b) :
    tentProfile a b x = b-x := by
  rw [tentProfile, min_eq_right (by linarith), max_eq_right (sub_nonneg.mpr hb)]

/-- An affine exponential primitive, valid also when the exponential parameter is zero. -/
theorem integral_affine_mul_cexp (q r s : ℂ) (a b : ℝ) :
    q^2 * (∫ x in a..b, (r*x+s)*exp (q*x)) =
      exp (q*b)*(q*(r*b+s)-r)-exp (q*a)*(q*(r*a+s)-r) := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => exp (q*x)*(q*(r*x+s)-r))
      (q^2*((r*x+s)*exp (q*x))) x := by
    have he := (Complex.ofRealCLM.hasDerivAt.const_mul q).cexp (x := x)
    have hl := ((((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul r).add_const s).const_mul q).sub_const r
    convert! he.mul hl using 1
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one]
    ring
  have hc : Continuous (fun x : ℝ => q^2*((r*x+s)*exp (q*x))) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hc.intervalIntegrable a b)
  rwa [intervalIntegral.integral_const_mul] at h

/-- Exact Laplace/Fourier transform of a tent on its support. -/
theorem integral_tentProfile_mul_cexp (a b : ℝ) (hab : a ≤ b) (q : ℂ) :
    q^2 * (∫ x in a..b, (tentProfile a b x : ℂ)*exp (q*x)) =
      exp (q*a)-2*exp (q*((a+b)/2 : ℝ))+exp (q*b) := by
  let m := (a+b)/2
  have ham : a ≤ m := by dsimp [m]; linarith
  have hmb : m ≤ b := by dsimp [m]; linarith
  have hc : Continuous (fun x : ℝ => (tentProfile a b x : ℂ)*exp (q*x)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable a m) (hc.intervalIntegrable m b), mul_add]
  have hl : (∫ x in a..m, (tentProfile a b x : ℂ)*exp (q*x)) =
      ∫ x in a..m, ((1 : ℂ)*x+(-a : ℝ))*exp (q*x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ham] at hx
    dsimp only
    rw [tentProfile_left hx.1 hx.2]
    push_cast
    ring
  have hr : (∫ x in m..b, (tentProfile a b x : ℂ)*exp (q*x)) =
      ∫ x in m..b, ((-1 : ℂ)*x+b)*exp (q*x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hmb] at hx
    dsimp only
    rw [tentProfile_right hx.1 hx.2]
    push_cast
    ring
  rw [hl,hr,integral_affine_mul_cexp,integral_affine_mul_cexp]
  dsimp [m]
  push_cast
  ring

/-- Enlarging the interval does not change a tent's transform. -/
theorem integral_tentProfile_mul_cexp_unit (a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 1) (q : ℂ) :
    (∫ x in (0 : ℝ)..1, (tentProfile a b x : ℂ)*exp (q*x)) =
      ∫ x in a..b, (tentProfile a b x : ℂ)*exp (q*x) := by
  have hc : Continuous (fun x : ℝ => (tentProfile a b x : ℂ)*exp (q*x)) := by fun_prop
  have hl : (∫ x in (0 : ℝ)..a, (tentProfile a b x : ℂ)*exp (q*x)) = 0 := by
    calc
      _ = ∫ _x in (0 : ℝ)..a, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le ha] at hx
        simp [tentProfile_eq_zero_left a b hx.2]
      _ = 0 := by simp
  have hr : (∫ x in b..(1 : ℝ), (tentProfile a b x : ℂ)*exp (q*x)) = 0 := by
    calc
      _ = ∫ _x in b..(1 : ℝ), (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hb] at hx
        simp [tentProfile_eq_zero_right a b hx.1]
      _ = 0 := by simp
  have h₁ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)
  have h₂ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 b) (hc.intervalIntegrable b 1)
  rw [hl,zero_add] at h₁
  rw [hr,add_zero] at h₂
  exact h₂.symm.trans h₁.symm

/-- Every real exponential weight has a strictly positive integral against a nonempty tent. -/
theorem integral_tentProfile_mul_exp_pos (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (q : ℝ) :
    0 < ∫ x in (0 : ℝ)..1, tentProfile a b x*Real.exp (q*x) := by
  apply intervalIntegral.integral_pos (by norm_num)
  · apply Continuous.continuousOn
    fun_prop
  · intro x _
    exact mul_nonneg (tentProfile_nonneg a b x) (Real.exp_pos _).le
  · refine ⟨(a+b)/2,⟨by linarith,by linarith⟩,?_⟩
    exact mul_pos (tentProfile_pos (by linarith) (by linarith)) (Real.exp_pos _)

/-- The zero-frequency coefficient is the exact triangle area. -/
theorem integral_tentProfile (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, tentProfile a b x) = (b-a)^2/4 := by
  let m := (a+b)/2
  have ham : a ≤ m := by dsimp [m]; linarith
  have hmb : m ≤ b := by dsimp [m]; linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((continuous_tentProfile a b).intervalIntegrable a m)
    ((continuous_tentProfile a b).intervalIntegrable m b)]
  have hl : (∫ x in a..m, tentProfile a b x) = ∫ x in a..m, x-a := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ham] at hx
    exact tentProfile_left hx.1 hx.2
  have hr : (∫ x in m..b, tentProfile a b x) = ∫ x in m..b, b-x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hmb] at hx
    exact tentProfile_right hx.1 hx.2
  rw [hl,hr,intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => a)
    (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_sub (f := fun _ : ℝ => b) (g := fun x : ℝ => x)
    (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
  simp only [integral_id,intervalIntegral.integral_const,smul_eq_mul]
  dsimp [m]
  ring

/-- Extending the support integral to the full unit interval preserves the exact area. -/
theorem integral_tentProfile_unit (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ x in (0 : ℝ)..1, tentProfile a b x) = (b-a)^2/4 := by
  have h := integral_tentProfile_mul_cexp_unit a b ha hb 0
  simp only [zero_mul,exp_zero,mul_one,intervalIntegral.integral_ofReal] at h
  have hr := Complex.ofReal_injective h
  exact hr.trans (integral_tentProfile a b hab)

/-- The mean is nonzero for every nonempty tent inside the period. -/
theorem periodOneCoefficient_tentProfile_zero (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    periodOneCoefficient (fun x => (tentProfile a b x : ℂ)) 0 = (((b-a)^2/4 : ℝ) : ℂ) := by
  rw [periodOneCoefficient,fourierCoeffOn_one]
  simp only [mul_zero,neg_zero,halfCoefficient,wave,Int.cast_zero,zero_mul,mul_zero,exp_zero,mul_one]
  rw [← mul_assoc]
  norm_num only [mul_one_div_cancel,one_mul]
  rw [intervalIntegral.integral_ofReal, integral_tentProfile_unit a b ha hab hb]

/-- A frequency-independent coefficient bound retains the scale through the triangle area. -/
theorem norm_periodOneCoefficient_tentProfile_le_area (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (n : ℤ) :
    ‖periodOneCoefficient (fun x => (tentProfile a b x : ℂ)) n‖ ≤ (b-a)^2/4 := by
  rw [periodOneCoefficient,fourierCoeffOn_one]
  unfold halfCoefficient
  rw [← mul_assoc]
  norm_num only [mul_one_div_cancel,one_mul]
  calc
    _ ≤ ∫ x in (0 : ℝ)..1, ‖(tentProfile a b x : ℂ)*wave (-(2*n)) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ∫ x in (0 : ℝ)..1, tentProfile a b x := by
      apply intervalIntegral.integral_congr
      intro x _
      simp [wave, Complex.norm_exp, Complex.norm_real, abs_of_nonneg (tentProfile_nonneg a b x)]
    _ = _ := integral_tentProfile_unit a b ha hab hb

/-- The original unit-period Fourier coefficient has the exact tent transform. -/
theorem periodOneCoefficient_tentProfile (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (n : ℤ) :
    (-2*(Real.pi : ℂ)*I*n)^2 * periodOneCoefficient (fun x => (tentProfile a b x : ℂ)) n =
      exp ((-2*(Real.pi : ℂ)*I*n)*a) -
      2*exp ((-2*(Real.pi : ℂ)*I*n)*((a+b)/2 : ℝ)) +
      exp ((-2*(Real.pi : ℂ)*I*n)*b) := by
  have hc : periodOneCoefficient (fun x => (tentProfile a b x : ℂ)) n =
      ∫ x in (0 : ℝ)..1, (tentProfile a b x : ℂ)*exp ((-2*(Real.pi : ℂ)*I*n)*x) := by
    rw [periodOneCoefficient, fourierCoeffOn_one]
    unfold halfCoefficient
    rw [← mul_assoc]
    norm_num only [mul_one_div_cancel, one_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    have he : wave (-(2*n)) x = exp ((-2*(Real.pi : ℂ)*I*n)*x) := by
      unfold wave
      congr 1
      push_cast
      ring
    rw [he]
  rw [hc, integral_tentProfile_mul_cexp_unit a b ha hb]
  exact integral_tentProfile_mul_cexp a b hab _

/-- Explicit quadratic decay at every integer frequency (including the harmless zero case). -/
theorem norm_periodOneCoefficient_tentProfile_mul_frequency_le (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (n : ℤ) :
    (2*Real.pi*|(n : ℝ)|)^2 * ‖periodOneCoefficient (fun x => (tentProfile a b x : ℂ)) n‖ ≤ 4 := by
  have hn := congrArg norm (periodOneCoefficient_tentProfile a b ha hab hb n)
  have he (x : ℝ) : ‖exp ((-2*(Real.pi : ℂ)*I*n)*x)‖ = 1 := by
    simp [Complex.norm_exp, mul_re, mul_im]
  have hq : ‖-2*(Real.pi : ℂ)*I*n‖ = 2*Real.pi*|(n : ℝ)| := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [norm_mul, norm_pow, hq] at hn
  rw [hn]
  calc
    _ ≤ ‖exp ((-2*(Real.pi : ℂ)*I*n)*a)-2*exp ((-2*(Real.pi : ℂ)*I*n)*((a+b)/2 : ℝ))‖ +
        ‖exp ((-2*(Real.pi : ℂ)*I*n)*b)‖ := norm_add_le _ _
    _ ≤ (‖exp ((-2*(Real.pi : ℂ)*I*n)*a)‖+
        ‖2*exp ((-2*(Real.pi : ℂ)*I*n)*((a+b)/2 : ℝ))‖) +
        ‖exp ((-2*(Real.pi : ℂ)*I*n)*b)‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ = 4 := by rw [norm_mul, he a, he ((a+b)/2), he b]; norm_num

end NLS.Fourier
