import NLS.Fourier.DyadicTentSum

/-! # The normalized lower coupling after the dyadic upper sum -/
noncomputable section
open Complex MeasureTheory Set intervalIntegral
open scoped ENNReal
namespace NLS.Fourier

/-- A unit-area tent at the end of the period, at the smallest upper scale. -/
def lowerDyadicTent (J : ℕ) (x : ℝ) : ℝ :=
  (4*4^J)*tentProfile (1-dyadicTentWidth J) 1 x

@[fun_prop] theorem continuous_lowerDyadicTent (J : ℕ) : Continuous (lowerDyadicTent J) := by
  unfold lowerDyadicTent
  fun_prop

theorem lowerDyadicTent_nonneg (J : ℕ) (x : ℝ) : 0 ≤ lowerDyadicTent J x := by
  exact mul_nonneg (by positivity) (tentProfile_nonneg _ _ _)

theorem lowerDyadicTent_eq_zero_before (J : ℕ) {x : ℝ} (hx : x ≤ 1-dyadicTentWidth J) :
    lowerDyadicTent J x = 0 := by rw [lowerDyadicTent,tentProfile_eq_zero_left _ _ hx,mul_zero]

theorem lowerDyadicTent_endpoints (J : ℕ) (hJ : 2 ≤ J) :
    lowerDyadicTent J 0 = 0 ∧ lowerDyadicTent J 1 = 0 := by
  have hd := dyadicTentWidth_le_quarter J hJ
  refine ⟨lowerDyadicTent_eq_zero_before J (by linarith),?_⟩
  rw [lowerDyadicTent,tentProfile_eq_zero_right _ _ (le_refl 1),mul_zero]

/-- The original Hilbert coefficients, with no change of Fourier convention. -/
def lowerDyadicTentCoefficients (J : ℕ) (hJ : 2 ≤ J) : Coeff 2 :=
  continuousPeriodOneCoefficients (fun x => (lowerDyadicTent J x : ℂ)) (by fun_prop)
    (by rw [(lowerDyadicTent_endpoints J hJ).1,(lowerDyadicTent_endpoints J hJ).2])

@[simp] theorem lowerDyadicTentCoefficients_apply (J : ℕ) (hJ : 2 ≤ J) (n : ℤ) :
    lowerDyadicTentCoefficients J hJ n = periodOneCoefficient (fun x => (lowerDyadicTent J x : ℂ)) n := by
  apply continuousPeriodOneCoefficients_apply

theorem circlePullback_lowerDyadicTentCoefficients (J : ℕ) (hJ : 2 ≤ J) :
    circlePullback (l2Synthesis (Coeff.periodDouble (lowerDyadicTentCoefficients J hJ)))
      =ᵐ[volume.restrict (Ioc 0 1)] fun x => (lowerDyadicTent J x : ℂ) := by
  apply circlePullback_continuousPeriodOneCoefficients

theorem periodOneCoefficient_lowerDyadicTent (J : ℕ) (n : ℤ) :
    periodOneCoefficient (fun x => (lowerDyadicTent J x : ℂ)) n =
      ((4*4^J : ℝ) : ℂ)*periodOneCoefficient
        (fun x => (tentProfile (1-dyadicTentWidth J) 1 x : ℂ)) n := by
  simp only [lowerDyadicTent,ofReal_mul,periodOneCoefficient]
  exact fourierCoeffOn.const_mul _ _ n (by norm_num)

/-- The scalar area and the zero-frequency coefficient are both exactly one. -/
theorem integral_lowerDyadicTent (J : ℕ) (hJ : 2 ≤ J) :
    (∫ x in (0 : ℝ)..1, lowerDyadicTent J x) = 1 := by
  have hd := dyadicTentWidth_pos J
  have hb := dyadicTentWidth_le_quarter J hJ
  unfold lowerDyadicTent
  rw [intervalIntegral.integral_const_mul,
    integral_tentProfile_unit (1-dyadicTentWidth J) 1 (by linarith) (by linarith) (le_refl 1)]
  have he := four_pow_mul_dyadicTentWidth_sq J
  nlinarith

@[simp] theorem lowerDyadicTentCoefficients_zero (J : ℕ) (hJ : 2 ≤ J) :
    lowerDyadicTentCoefficients J hJ 0 = 1 := by
  rw [lowerDyadicTentCoefficients_apply,periodOneCoefficient_eq_wave_integral]
  simp only [mul_zero,neg_zero,wave,Int.cast_zero,zero_mul,mul_zero,exp_zero,mul_one,
    intervalIntegral.integral_ofReal,integral_lowerDyadicTent J hJ,ofReal_one]

/-- The area controls every original coefficient. -/
theorem norm_lowerDyadicTentCoefficients_le_one (J : ℕ) (hJ : 2 ≤ J) (n : ℤ) :
    ‖lowerDyadicTentCoefficients J hJ n‖ ≤ 1 := by
  have hd := dyadicTentWidth_pos J
  have hb := dyadicTentWidth_le_quarter J hJ
  have h := norm_periodOneCoefficient_tentProfile_le_area (1-dyadicTentWidth J) 1
    (by linarith) (by linarith) (le_refl 1) n
  rw [lowerDyadicTentCoefficients_apply,periodOneCoefficient_lowerDyadicTent,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4*4^J)]
  have he := four_pow_mul_dyadicTentWidth_sq J
  nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 4*4^J)]

/-- Quadratic decay retains the smallest spatial scale. -/
theorem norm_lowerDyadicTentCoefficients_tail (J : ℕ) (hJ : 2 ≤ J) (n : ℤ) :
    |(n : ℝ)|^2 * ‖lowerDyadicTentCoefficients J hJ n‖ ≤ (4 : ℝ)^J := by
  have hd := dyadicTentWidth_pos J
  have hb := dyadicTentWidth_le_quarter J hJ
  have h := norm_periodOneCoefficient_tentProfile_mul_frequency_le (1-dyadicTentWidth J) 1
    (by linarith) (by linarith) (le_refl 1) n
  have hπ : 4 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hn := norm_nonneg (periodOneCoefficient (fun x => (tentProfile (1-dyadicTentWidth J) 1 x : ℂ)) n)
  have hh : |(n : ℝ)|^2 * ‖periodOneCoefficient (fun x => (tentProfile (1-dyadicTentWidth J) 1 x : ℂ)) n‖ ≤ 1/4 := by
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) hn]
  rw [lowerDyadicTentCoefficients_apply,periodOneCoefficient_lowerDyadicTent,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4*4^J)]
  nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 4*4^J)]

/-- Removing the single mean coefficient permits the zero-mean envelope estimate. -/
theorem norm_exponent_lowerDyadicTentCoefficients_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h2p : (2 : ℝ≥0∞) ≤ p) (J : ℕ) (hJ : 2 ≤ J) :
    ‖Coeff.exponentInclusion h2p (lowerDyadicTentCoefficients J hJ)‖ ≤
      1+(8*(2 : ℝ)^J)^(1/p.toReal) := by
  let a := Coeff.exponentInclusion h2p (lowerDyadicTentCoefficients J hJ)
  let c : Coeff p := lp.single p 0 (1 : ℂ)
  let b := a-c
  have hb0 : b 0 = 0 := by
    change lowerDyadicTentCoefficients J hJ 0 - (lp.single p 0 (1 : ℂ) : Coeff p) 0 = 0
    rw [lowerDyadicTentCoefficients_zero,lp.single_apply_self,sub_self]
  have hbn (n : ℤ) (hn : n ≠ 0) : b n = lowerDyadicTentCoefficients J hJ n := by
    change lowerDyadicTentCoefficients J hJ n - (lp.single p 0 (1 : ℂ) : Coeff p) n = _
    rw [lp.single_apply_ne _ _ _ hn,sub_zero]
  have hbmax (n : ℤ) : ‖b n‖ ≤ 1 := by
    by_cases hn : n = 0
    · simp [hn,hb0]
    · rw [hbn n hn]
      exact norm_lowerDyadicTentCoefficients_le_one J hJ n
  have hbtail (n : ℤ) : |(n : ℝ)|^2 * ‖b n‖ ≤ 1*((2 : ℝ)^J)^2 := by
    by_cases hn : n = 0
    · simp [hn,hb0]
    · rw [hbn n hn,one_mul,← pow_mul,Nat.mul_comm J 2,pow_mul]
      norm_num only [show (2 : ℝ)^2 = 4 by norm_num]
      exact norm_lowerDyadicTentCoefficients_tail J hJ n
  have h := Coeff.norm_le_of_uniform_quadratic_envelope hp b 1 (2^J) (by norm_num) (by positivity) hb0 hbmax hbtail
  have ha : a = c+b := by dsimp [b]; abel
  have hc : ‖c‖ = 1 := by
    simp [c,lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))]
  change ‖a‖ ≤ _
  rw [ha]
  exact (norm_add_le c b).trans (by simpa only [hc,one_mul] using add_le_add (le_refl (1 : ℝ)) h)

/-- The same scale/exponent choice as the upper sum gives a uniform lower norm of nine. -/
theorem norm_lowerDyadicTentCoefficients_twice_exponent_le
    (P : ℕ) [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 3 ≤ P) :
    ‖Coeff.exponentInclusion (show (2 : ℝ≥0∞) ≤ P by exact_mod_cast (show 2 ≤ P by omega))
      (lowerDyadicTentCoefficients (2*P) (by omega))‖ ≤ 9 := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have h₂ : (8 : ℝ) ≤ 2^P := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hP
    norm_num at h
    exact h
  have hbase : 8*(2 : ℝ)^(2*P) ≤ 8^P := by
    calc
      _ ≤ (2 : ℝ)^P*2^(2*P) := mul_le_mul_of_nonneg_right h₂ (by positivity)
      _ = _ := by rw [pow_mul,← mul_pow]; norm_num
  have hroot : (8*(2 : ℝ)^(2*P))^(1/(P : ℝ)) ≤ 8 := by
    have h := Real.rpow_le_rpow (by positivity) hbase (by positivity : (0 : ℝ) ≤ 1/(P : ℝ))
    rw [← Real.rpow_natCast (8 : ℝ) P,← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8),
      mul_one_div_cancel hP0.ne',Real.rpow_one] at h
    exact h
  have h := norm_exponent_lowerDyadicTentCoefficients_le (by simp : (P : ℝ≥0∞) ≠ ⊤)
    (show (2 : ℝ≥0∞) ≤ P by exact_mod_cast (show 2 ≤ P by omega)) (2*P) (by omega)
  simp only [ENNReal.toReal_natCast] at h
  linarith

/-- The late interaction has its full exponential lower bound. -/
theorem integral_lowerDyadicTent_exp_lower (J : ℕ) (hJ : 2 ≤ J) (H : ℝ) (hH : 0 ≤ H) :
    Real.exp (2*H*(1-dyadicTentWidth J)) ≤
      ∫ x in (0 : ℝ)..1, lowerDyadicTent J x*Real.exp (2*H*x) := by
  have hc : Continuous (fun x => lowerDyadicTent J x*Real.exp (2*H*(1-dyadicTentWidth J))) := by fun_prop
  have hg : Continuous (fun x => lowerDyadicTent J x*Real.exp (2*H*x)) := by fun_prop
  calc
    _ = ∫ x in (0 : ℝ)..1, lowerDyadicTent J x*Real.exp (2*H*(1-dyadicTentWidth J)) := by
      rw [intervalIntegral.integral_mul_const,integral_lowerDyadicTent J hJ,one_mul]
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hc.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
      intro x _
      by_cases hx : x ≤ 1-dyadicTentWidth J
      · rw [lowerDyadicTent_eq_zero_before J hx,zero_mul,zero_mul]
      · apply mul_le_mul_of_nonneg_left _ (lowerDyadicTent_nonneg J x)
        apply Real.exp_le_exp.mpr
        nlinarith

end NLS.Fourier
