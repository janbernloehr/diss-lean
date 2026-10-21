import NLS.Fourier.PeriodicHolomorphicCoefficients
import Mathlib.Analysis.Complex.LocallyUniformLimit

noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
namespace NLS.Fourier

/-- The complex Fourier series in the original physical period-one convention. -/
def periodOneComplexSynthesis (c : ℤ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, c n*complexPeriodOneWave n z

/-- The norm of a complex Fourier wave depends only on height and signed frequency. -/
theorem norm_complexPeriodOneWave (n : ℤ) (z : ℂ) :
    ‖complexPeriodOneWave n z‖ = Real.exp (-2*Real.pi*(n:ℝ)*z.im) := by
  rw [complexPeriodOneWave,Complex.norm_exp]
  congr 1
  norm_num [Complex.mul_re,Complex.mul_im]

/-- The two-sided geometric majorant is summable for every positive decay rate. -/
theorem summable_exp_neg_abs_int (d : ℝ) (hd : 0 < d) :
    Summable (fun n : ℤ => Real.exp (-d*|(n:ℝ)|)) := by
  have hq : Real.exp (-d) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := summable_geometric_of_lt_one (Real.exp_pos (-d)).le hq
  apply Summable.of_nat_of_neg_add_one
  · simpa only [Int.cast_natCast,Nat.abs_cast,mul_comm (-d),Real.exp_nat_mul] using h
  · have he (n : ℕ) : Real.exp (-d*|((-((n:ℤ)+1):ℤ):ℝ)|) =
        Real.exp (-d)*Real.exp (-d)^n := by
      simp only [Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one,abs_neg,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)+1),← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      ring
    simp only [he]
    exact h.mul_left (Real.exp (-d))

/-- Exponential coefficient decay yields one uniform summable bound on every narrower strip. -/
theorem norm_complex_fourier_term_le (c : ℤ → ℂ) (M b r : ℝ) (hM : 0 ≤ M)
    (hc : ∀ n : ℤ, ‖c n‖ ≤ M*Real.exp (-b*|(n:ℝ)|))
    (z : ℂ) (hz : |z.im| ≤ r) (n : ℤ) :
    ‖c n*complexPeriodOneWave n z‖ ≤ M*Real.exp (-(b-2*Real.pi*r)*|(n:ℝ)|) := by
  rw [norm_mul,norm_complexPeriodOneWave]
  calc
    _ ≤ (M*Real.exp (-b*|(n:ℝ)|))*Real.exp (-2*Real.pi*(n:ℝ)*z.im) :=
      mul_le_mul_of_nonneg_right (hc n) (Real.exp_pos _).le
    _ = M*Real.exp (-b*|(n:ℝ)|+-2*Real.pi*(n:ℝ)*z.im) := by
      rw [mul_assoc,← Real.exp_add]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
      have h₁ := neg_le_abs ((n:ℝ)*z.im)
      rw [abs_mul] at h₁
      have h₂ := mul_le_mul_of_nonneg_left hz (abs_nonneg (n:ℝ))
      have h₃ := mul_le_mul_of_nonneg_left (h₁.trans h₂) (by positivity : 0 ≤ 2*Real.pi)
      nlinarith

/-- The full complex Fourier series is absolutely summable at every interior point. -/
theorem summable_norm_complex_fourier (c : ℤ → ℂ) (M b : ℝ) (hM : 0 ≤ M)
    (hc : ∀ n : ℤ, ‖c n‖ ≤ M*Real.exp (-b*|(n:ℝ)|))
    (z : ℂ) (hz : |z.im| < b/(2*Real.pi)) :
    Summable (fun n : ℤ => ‖c n*complexPeriodOneWave n z‖) := by
  have hd : 0 < b-2*Real.pi*|z.im| := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2*Real.pi)).mp hz
    nlinarith
  apply ((summable_exp_neg_abs_int _ hd).mul_left M).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  exact norm_complex_fourier_term_le c M b |z.im| hM hc z le_rfl

/-- Local uniform summability constructs a holomorphic extension on the exact open strip. -/
theorem analyticOnNhd_periodOneComplexSynthesis (c : ℤ → ℂ) (M b : ℝ) (hM : 0 ≤ M)
    (hc : ∀ n : ℤ, ‖c n‖ ≤ M*Real.exp (-b*|(n:ℝ)|)) :
    AnalyticOnNhd ℂ (periodOneComplexSynthesis c) {z : ℂ | |z.im| < b/(2*Real.pi)} := by
  intro z hz
  change |z.im| < b/(2*Real.pi) at hz
  obtain ⟨r,hzr,hr⟩ := exists_between hz
  have hd : 0 < b-2*Real.pi*r := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2*Real.pi)).mp hr
    nlinarith
  have hopen : IsOpen {w : ℂ | |w.im| < r} := isOpen_lt Complex.continuous_im.abs continuous_const
  have hdiff : DifferentiableOn ℂ (periodOneComplexSynthesis c) {w : ℂ | |w.im| < r} := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      ((summable_exp_neg_abs_int _ hd).mul_left M)
    · intro n
      unfold complexPeriodOneWave
      fun_prop
    · exact hopen
    · intro n w hw
      exact norm_complex_fourier_term_le c M b r hM hc w (le_of_lt hw) n
  exact hdiff.analyticAt (hopen.mem_nhds hzr)

/-- The extension is period one at every complex argument. -/
theorem periodOneComplexSynthesis_periodic (c : ℤ → ℂ) :
    Function.Periodic (periodOneComplexSynthesis c) 1 := by
  intro z
  unfold periodOneComplexSynthesis
  apply tsum_congr
  intro n
  rw [complexPeriodOneWave_periodic n z]

/-- Complex waves restrict to the original even-frequency real waves. -/
theorem complexPeriodOneWave_ofReal (n : ℤ) (x : ℝ) :
    complexPeriodOneWave n x = wave (2*n) x := by
  unfold complexPeriodOneWave wave
  push_cast
  congr 1
  ring

/-- The exact raw Fourier coefficients of a horizontal translate. -/
def complexHorizontalCoefficients (c : ℤ → ℂ) (y : ℝ) (n : ℤ) : ℂ :=
  (Real.exp (-2*Real.pi*y*(n:ℝ)):ℂ)*c n

/-- Interior horizontal coefficient sequences are absolutely summable. -/
theorem memlp_one_complexHorizontalCoefficients (c : ℤ → ℂ) (M b : ℝ) (hM : 0 ≤ M)
    (hc : ∀ n : ℤ, ‖c n‖ ≤ M*Real.exp (-b*|(n:ℝ)|))
    (y : ℝ) (hy : |y| < b/(2*Real.pi)) :
    Memℓp (complexHorizontalCoefficients c y) 1 := by
  have he (n : ℤ) : c n*complexPeriodOneWave n ((0:ℂ)+y*I) =
      complexHorizontalCoefficients c y n := by
    have hh := complexPeriodOneWave_horizontal n 0 y
    simp only [Complex.ofReal_zero] at hh
    rw [hh]
    simp [complexPeriodOneWave,complexHorizontalCoefficients,mul_comm]
  apply (memℓp_gen_iff (by norm_num : 0 < (1:ENNReal).toReal)).mpr
  simp only [ENNReal.toReal_one,Real.rpow_one]
  have h := summable_norm_complex_fourier c M b hM hc ((0:ℂ)+y*I) (by simpa using hy)
  simpa only [he] using h

/-- The actual l1 data for each interior horizontal trace. -/
def complexHorizontalData (c : ℤ → ℂ) (M b : ℝ) (hM : 0 ≤ M)
    (hc : ∀ n : ℤ, ‖c n‖ ≤ M*Real.exp (-b*|(n:ℝ)|))
    (y : ℝ) (hy : |y| < b/(2*Real.pi)) : Coeff 1 :=
  ⟨complexHorizontalCoefficients c y,memlp_one_complexHorizontalCoefficients c M b hM hc y hy⟩

/-- Interior traces are the actual continuous period-one Fourier synthesis. -/
theorem periodOneComplexSynthesis_horizontal (c : ℤ → ℂ) (M b : ℝ) (hM : 0 ≤ M)
    (hc : ∀ n : ℤ, ‖c n‖ ≤ M*Real.exp (-b*|(n:ℝ)|))
    (y : ℝ) (hy : |y| < b/(2*Real.pi)) (x : ℝ) :
    periodOneComplexSynthesis c ((x:ℂ)+y*I) =
      periodOneSynthesis (complexHorizontalData c M b hM hc y hy) x := by
  rw [periodOneComplexSynthesis,periodOneSynthesis_eq_tsum]
  apply tsum_congr
  intro n
  change c n*complexPeriodOneWave n ((x:ℂ)+y*I) = complexHorizontalCoefficients c y n*wave (2*n) x
  rw [complexPeriodOneWave_horizontal,complexPeriodOneWave_ofReal,complexHorizontalCoefficients]
  ring

/-- Taking actual unit-interval Fourier integrals recovers every interior shifted coefficient. -/
theorem periodOneCoefficient_complexSynthesis_horizontal (c : ℤ → ℂ) (M b : ℝ) (hM : 0 ≤ M)
    (hc : ∀ n : ℤ, ‖c n‖ ≤ M*Real.exp (-b*|(n:ℝ)|))
    (y : ℝ) (hy : |y| < b/(2*Real.pi)) (n : ℤ) :
    periodOneCoefficient (fun x : ℝ => periodOneComplexSynthesis c ((x:ℂ)+y*I)) n =
      complexHorizontalCoefficients c y n := by
  have he := funext (periodOneComplexSynthesis_horizontal c M b hM hc y hy)
  rw [he,periodOneCoefficient_synthesis]
  rfl

end NLS.Fourier
