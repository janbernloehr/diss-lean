import NLS.Fourier.SobolevSynthesis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.AtTopBot.Interval

/-! # Coefficients of the series printed in Lemma A.5

These estimates concern the literal one-sided coefficient sequence. They do
not yet assert continuity of the physical Fourier series.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.Fourier

/-- The coefficient printed in A.5, with the prescribed lower cutoff n=2. -/
def printedChirpCoefficient (n : ℤ) : ℂ :=
  if 2 ≤ n then
    Complex.exp (Complex.I*((n : ℝ)*Real.log (n : ℝ))) /
      ((Real.sqrt (n : ℝ)*(Real.log (n : ℝ))^2 : ℝ) : ℂ)
  else 0

theorem norm_printedChirpCoefficient (n : ℤ) (hn : 2 ≤ n) :
    ‖printedChirpCoefficient n‖ = 1/(Real.sqrt (n : ℝ)*(Real.log (n : ℝ))^2) := by
  simp [printedChirpCoefficient,hn,Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs]

theorem norm_printedChirpCoefficient_sq (n : ℤ) (hn : 2 ≤ n) :
    ‖printedChirpCoefficient n‖^2 = 1/((n : ℝ)*(Real.log (n : ℝ))^4) := by
  rw [norm_printedChirpCoefficient n hn,div_pow,one_pow,mul_pow,
    Real.sq_sqrt (by exact_mod_cast (show 0 ≤ n by omega)),← pow_mul]

private theorem summable_inverse_nat_log_four :
    Summable (fun n : ℕ => 1/((n : ℝ)*(Real.log (n : ℝ))^4)) := by
  apply (summable_condensed_iff_of_eventually_nonneg
    (Eventually.of_forall (fun n => by positivity)) ?_).mp
  · have hs : Summable (fun k : ℕ => (1/(Real.log 2)^4)*(1/(k : ℝ)^4)) :=
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (4 : ℕ))).mul_left _
    apply hs.congr
    intro k
    simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    have htwo : (2 : ℝ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with k hk
    have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    apply one_div_le_one_div_of_le
    · exact mul_pos hk0 (pow_pos (Real.log_pos (by exact_mod_cast (show 1 < k by omega))) _)
    · gcongr <;> omega

/-- The literal printed coefficients are square summable. -/
theorem memlp_printedChirpCoefficient_two : Memℓp printedChirpCoefficient 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · apply summable_inverse_nat_log_four.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact (norm_printedChirpCoefficient_sq n (by exact_mod_cast hn)).symm
  · have h (n : ℕ) : ¬(2 : ℤ) ≤ -(n : ℤ) := by omega
    simp [printedChirpCoefficient,h]

/-- Exact real powers of the coefficient magnitudes, retaining the printed logarithm. -/
theorem norm_printedChirpCoefficient_rpow (n : ℤ) (hn : 2 ≤ n) (q : ℝ) :
    ‖printedChirpCoefficient n‖^q =
      1/((n : ℝ)^(q/2)*(Real.log (n : ℝ))^(2*q)) := by
  have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (show 0 ≤ n by omega)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  rw [norm_printedChirpCoefficient n hn,Real.div_rpow (by positivity) (by positivity),
    Real.one_rpow,Real.mul_rpow (Real.sqrt_nonneg _) (sq_nonneg _),Real.sqrt_eq_rpow,
    ← Real.rpow_mul hn0,← Real.rpow_two (Real.log (n : ℝ)),
    ← Real.rpow_mul (Real.log_nonneg hn1)]
  congr 3
  ring

/-- The literal printed sequence belongs to no Banach coefficient space below two. -/
theorem not_memlp_printedChirpCoefficient_below_two {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp2 : p < 2) : ¬Memℓp printedChirpCoefficient p := by
  intro h
  have hpt : p ≠ ⊤ := ne_of_lt (hp2.trans_le le_top)
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hpt
  have hr2 : p.toReal < 2 := by
    simpa only [ENNReal.toReal_ofNat] using (ENNReal.toReal_lt_toReal hpt (by simp)).mpr hp2
  let δ : ℝ := (1-p.toReal/2)/2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  let q : ℝ := p.toReal/2+δ
  have hq : q < 1 := by dsimp only [q,δ]; linarith
  have ht : Tendsto (fun n : ℕ => (Real.log (n : ℝ))^(2*p.toReal)/(n : ℝ)^δ)
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (2*p.toReal) hδ).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hs : Summable (fun n : ℕ => ‖printedChirpCoefficient (n : ℤ)‖^p.toReal) :=
    (h.summable hp0).comp_injective (fun a b hab => by exact_mod_cast hab)
  have hqsum : Summable (fun n : ℕ => 1/(n : ℝ)^q) := by
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop (2 : ℕ),ht.eventually_lt_const (by norm_num : (0 : ℝ)<1)] with n hn hb
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    have hl : (Real.log (n : ℝ))^(2*p.toReal) ≤ (n : ℝ)^δ :=
      ((div_lt_one (Real.rpow_pos_of_pos hn0 δ)).mp hb).le
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),
      norm_printedChirpCoefficient_rpow n (by exact_mod_cast hn)]
    change 1/(n : ℝ)^(p.toReal/2+δ) ≤ _
    rw [Real.rpow_add hn0]
    exact one_div_le_one_div_of_le
      (mul_pos (Real.rpow_pos_of_pos hn0 _) (Real.rpow_pos_of_pos (Real.log_pos hn1) _))
      (mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hn0.le _))
  exact (not_lt_of_ge hq.le) (Real.summable_one_div_nat_rpow.mp hqsum)

/-- Exact coefficient-space threshold, including the infinity endpoint. -/
theorem memlp_printedChirpCoefficient_iff {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Memℓp printedChirpCoefficient p ↔ 2 ≤ p := by
  constructor
  · intro h
    by_contra hp
    exact not_memlp_printedChirpCoefficient_below_two (lt_of_not_ge hp) h
  · exact memlp_printedChirpCoefficient_two.of_exponent_ge

/-- The literal coefficients as Hilbert Fourier data. -/
def printedChirpL2Coefficients : Coeff 2 :=
  ⟨printedChirpCoefficient,memlp_printedChirpCoefficient_two⟩

/-- A genuine physical period-two L2 realization of the printed coefficient sequence. -/
def printedChirpL2 : MeasureTheory.Lp ℂ 2 (AddCircle.haarAddCircle (T := (2 : ℝ))) :=
  l2Synthesis printedChirpL2Coefficients

/-- Its actual Fourier coefficients retain exactly the printed phases and amplitudes. -/
theorem fourierCoeff_printedChirpL2 (n : ℤ) :
    fourierCoeff printedChirpL2 n = printedChirpCoefficient n :=
  fourierCoeff_l2Synthesis printedChirpL2Coefficients n

/-- The actual Fourier series converges in the physical L2 norm. -/
theorem hasSum_printedChirpL2 :
    HasSum (fun n : ℤ => printedChirpCoefficient n • fourierLp (T := (2 : ℝ)) 2 n) printedChirpL2 := by
  simpa only [fourierCoeff_printedChirpL2] using hasSum_fourier_series_L2 printedChirpL2

/-- The exact positive-index partial sums printed in A.5 converge in L2. -/
theorem tendsto_printedChirpL2_partialSums :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (2 : ℤ) N,
      printedChirpCoefficient n • fourierLp (T := (2 : ℝ)) 2 n) atTop (𝓝 printedChirpL2) := by
  have he (N : ℕ) : (∑ n ∈ Finset.Icc (2 : ℤ) N,
      printedChirpCoefficient n • fourierLp (T := (2 : ℝ)) 2 n) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, printedChirpCoefficient n • fourierLp (T := (2 : ℝ)) 2 n := by
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hout
      have hlow : ¬(2 : ℤ) ≤ n := by
        simp only [Finset.mem_Icc] at hn hout
        omega
      simp [printedChirpCoefficient,hlow]
  simpa only [he,Function.comp_def] using hasSum_printedChirpL2.comp (Finset.tendsto_Icc_neg (R := ℤ))

/-- The actual physical realization has the same sharp Fourier-Lebesgue threshold. -/
theorem memlp_fourierCoeff_printedChirpL2_iff {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Memℓp (fourierCoeff printedChirpL2) p ↔ 2 ≤ p := by
  simp only [show fourierCoeff printedChirpL2 = printedChirpCoefficient from
    funext fourierCoeff_printedChirpL2,memlp_printedChirpCoefficient_iff]

end NLS.Fourier
