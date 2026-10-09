import NLS.Fourier.NormalizedDyadicTent
import NLS.SequenceSpaces.UniformQuadraticEnvelope
import NLS.SequenceSpaces.ExponentEmbedding

/-! # A continuous dyadic family with uniformly bounded Fourier coefficients

The finite physical sum retains its actual Fourier integrals. Its coefficient
bound is independent of the number of scales, while its weighted interaction
counts the sufficiently fine scales.
-/
noncomputable section
open Complex MeasureTheory Set intervalIntegral
open scoped ENNReal
namespace NLS.Fourier

/-- The signed, area-normalized physical sum over scales two through J. -/
def dyadicTentSum (J : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 J, normalizedDyadicTent j x

@[fun_prop] theorem continuous_dyadicTentSum (J : ℕ) : Continuous (dyadicTentSum J) := by
  unfold dyadicTentSum
  fun_prop

theorem dyadicTentSum_endpoints (J : ℕ) : dyadicTentSum J 0 = 0 ∧ dyadicTentSum J 1 = 0 := by
  constructor
  · apply Finset.sum_eq_zero
    intro j hj
    exact (normalizedDyadicTent_endpoints j (Finset.mem_Icc.mp hj).1).1
  · apply Finset.sum_eq_zero
    intro j hj
    exact (normalizedDyadicTent_endpoints j (Finset.mem_Icc.mp hj).1).2

/-- The smallest scale leaves a definite empty interval at both ends of the period. -/
theorem dyadicTentSum_eq_zero_near_ends (J : ℕ) {x : ℝ}
    (hx : x ≤ dyadicTentWidth J ∨ 1-dyadicTentWidth J ≤ x) : dyadicTentSum J x = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨hj₂,hjJ⟩ := Finset.mem_Icc.mp hj
  have hd := dyadicTentWidth_pos j
  have hb := dyadicTentWidth_le_quarter j hj₂
  have hmono : dyadicTentWidth J ≤ dyadicTentWidth j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hjJ
  rw [normalizedDyadicTent,oddTentProfile_eq_zero_near_ends _ _ (by linarith) (by linarith) ?_,mul_zero]
  rcases hx with hx | hx
  · exact Or.inl (hx.trans hmono)
  · exact Or.inr (by linarith)

/-- Coefficients of the physical sum are the sum of the original unit-period coefficients. -/
theorem periodOneCoefficient_dyadicTentSum (J : ℕ) (n : ℤ) :
    periodOneCoefficient (fun x => (dyadicTentSum J x : ℂ)) n =
      ∑ j ∈ Finset.Icc 2 J, periodOneCoefficient (fun x => (normalizedDyadicTent j x : ℂ)) n := by
  simp only [periodOneCoefficient_eq_wave_integral,dyadicTentSum,ofReal_sum,Finset.sum_mul]
  apply intervalIntegral.integral_finsetSum
  intro j _
  exact (by fun_prop : Continuous (fun x => (normalizedDyadicTent j x : ℂ)*wave (-(2*n)) x)).intervalIntegrable _ _

@[simp] theorem periodOneCoefficient_dyadicTentSum_zero (J : ℕ) :
    periodOneCoefficient (fun x => (dyadicTentSum J x : ℂ)) 0 = 0 := by
  rw [periodOneCoefficient_dyadicTentSum]
  simp only [periodOneCoefficient_normalizedDyadicTent_zero,Finset.sum_const_zero]

/-- Uniform coefficient control does not grow with the number of tents. -/
theorem norm_periodOneCoefficient_dyadicTentSum_le (J : ℕ) (n : ℤ) :
    ‖periodOneCoefficient (fun x => (dyadicTentSum J x : ℂ)) n‖ ≤ 80 := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [periodOneCoefficient_dyadicTentSum]
  apply (norm_sum_le _ _).trans
  exact sum_norm_le_of_dyadic_envelopes (Finset.Icc 2 J) _ n hn
    (fun j hj => norm_periodOneCoefficient_normalizedDyadicTent_low j (Finset.mem_Icc.mp hj).1 n)
    (fun j hj => norm_periodOneCoefficient_normalizedDyadicTent_high j (Finset.mem_Icc.mp hj).1 n)

/-- The smallest scale controls the quadratic tail, still without a factor counting the scales. -/
theorem norm_periodOneCoefficient_dyadicTentSum_tail (J : ℕ) (n : ℤ) :
    |(n : ℝ)|^2 * ‖periodOneCoefficient (fun x => (dyadicTentSum J x : ℂ)) n‖ ≤ 16*(4 : ℝ)^J := by
  rw [periodOneCoefficient_dyadicTentSum]
  calc
    _ ≤ |(n : ℝ)|^2 * ∑ j ∈ Finset.Icc 2 J,
        ‖periodOneCoefficient (fun x => (normalizedDyadicTent j x : ℂ)) n‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (sq_nonneg _)
    _ = ∑ j ∈ Finset.Icc 2 J, |(n : ℝ)|^2 *
        ‖periodOneCoefficient (fun x => (normalizedDyadicTent j x : ℂ)) n‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.Icc 2 J, 8*(4 : ℝ)^j := Finset.sum_le_sum (fun j hj =>
      norm_periodOneCoefficient_normalizedDyadicTent_high j (Finset.mem_Icc.mp hj).1 n)
    _ = 8*∑ j ∈ Finset.Icc 2 J, (4 : ℝ)^j := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      have h := sum_four_pow_le (Finset.Icc 2 J) J (fun j hj => (Finset.mem_Icc.mp hj).2)
      linarith

/-- Actual Hilbert coefficients of the continuous sum. -/
def dyadicTentSumCoefficients (J : ℕ) : Coeff 2 :=
  continuousPeriodOneCoefficients (fun x => (dyadicTentSum J x : ℂ)) (by fun_prop)
    (by rw [(dyadicTentSum_endpoints J).1,(dyadicTentSum_endpoints J).2])

@[simp] theorem dyadicTentSumCoefficients_apply (J : ℕ) (n : ℤ) :
    dyadicTentSumCoefficients J n = periodOneCoefficient (fun x => (dyadicTentSum J x : ℂ)) n := by
  apply continuousPeriodOneCoefficients_apply

theorem circlePullback_dyadicTentSumCoefficients (J : ℕ) :
    circlePullback (l2Synthesis (Coeff.periodDouble (dyadicTentSumCoefficients J)))
      =ᵐ[volume.restrict (Ioc 0 1)] fun x => (dyadicTentSum J x : ℂ) := by
  apply circlePullback_continuousPeriodOneCoefficients

/-- Every included scale has nonnegative interaction at nonnegative height. -/
theorem integral_normalizedDyadicTent_nonneg (j : ℕ) (hj : 2 ≤ j) (H : ℝ) (hH : 0 ≤ H) :
    0 ≤ ∫ x in (0 : ℝ)..1, normalizedDyadicTent j x*Real.exp (-2*H*x) := by
  apply le_trans _ (integral_normalizedDyadicTent_lower j hj H hH)
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  have hd := dyadicTentWidth_le_quarter j hj
  nlinarith

/-- Integration commutes with the finite physical sum. -/
theorem integral_dyadicTentSum (J : ℕ) (H : ℝ) :
    (∫ x in (0 : ℝ)..1, dyadicTentSum J x*Real.exp (-2*H*x)) =
      ∑ j ∈ Finset.Icc 2 J, ∫ x in (0 : ℝ)..1, normalizedDyadicTent j x*Real.exp (-2*H*x) := by
  simp only [dyadicTentSum,Finset.sum_mul]
  apply intervalIntegral.integral_finsetSum
  intro j _
  exact (by fun_prop : Continuous (fun x => normalizedDyadicTent j x*Real.exp (-2*H*x))).intervalIntegrable _ _

/-- Any collection of sufficiently fine scales contributes at least its cardinality divided by four. -/
theorem integral_dyadicTentSum_lower (J K : ℕ) (hK : 2 ≤ K) (H : ℝ) (hH : 3 ≤ H)
    (hscale : H*dyadicTentWidth K ≤ 1/8) :
    ((Finset.Icc K J).card : ℝ)/4 ≤ ∫ x in (0 : ℝ)..1, dyadicTentSum J x*Real.exp (-2*H*x) := by
  rw [integral_dyadicTentSum]
  calc
    _ = ∑ _j ∈ Finset.Icc K J, (1/4 : ℝ) := by simp; ring
    _ ≤ ∑ j ∈ Finset.Icc K J, ∫ x in (0 : ℝ)..1, normalizedDyadicTent j x*Real.exp (-2*H*x) := by
      apply Finset.sum_le_sum
      intro j hj
      apply integral_normalizedDyadicTent_ge_quarter j (hK.trans (Finset.mem_Icc.mp hj).1) H hH
      have hd : dyadicTentWidth j ≤ dyadicTentWidth K :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Finset.mem_Icc.mp hj).1
      exact (mul_le_mul_of_nonneg_left hd (by linarith)).trans hscale
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc hK le_rfl)
      intro j hj _
      exact integral_normalizedDyadicTent_nonneg j (Finset.mem_Icc.mp hj).1 H (by linarith)

/-- At height 2^P, scales through 2P give a linearly growing interaction. -/
theorem integral_dyadicTentSum_pow_height (P : ℕ) (hP : 3 ≤ P) :
    ((P-2 : ℕ) : ℝ)/4 ≤ ∫ x in (0 : ℝ)..1, dyadicTentSum (2*P) x*Real.exp (-2*(2 : ℝ)^P*x) := by
  have hH : (3 : ℝ) ≤ 2^P := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 2 ≤ P by omega)
    norm_num at h
    linarith
  have hscale : (2 : ℝ)^P * dyadicTentWidth (P+3) ≤ 1/8 := by
    unfold dyadicTentWidth
    rw [pow_add,div_pow]
    field_simp
    norm_num
  have h := integral_dyadicTentSum_lower (2*P) (P+3) (by omega) (2^P) hH hscale
  have hcard : (Finset.Icc (P+3) (2*P)).card = P-2 := by rw [Nat.card_Icc]; omega
  simpa only [hcard] using h

/-- The uniform and tail bounds control the actual original coefficient norm at every finite p>=2. -/
theorem norm_exponent_dyadicTentSumCoefficients_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h2p : (2 : ℝ≥0∞) ≤ p) (J : ℕ) :
    ‖Coeff.exponentInclusion h2p (dyadicTentSumCoefficients J)‖ ≤
      80*(8*(2 : ℝ)^J)^(1/p.toReal) := by
  apply Coeff.norm_le_of_uniform_quadratic_envelope hp _ 80 (2^J) (by norm_num) (by positivity)
  · simp [Coeff.exponentInclusion_apply]
  · intro n
    simpa only [Coeff.exponentInclusion_apply,dyadicTentSumCoefficients_apply] using
      norm_periodOneCoefficient_dyadicTentSum_le J n
  · intro n
    have h := norm_periodOneCoefficient_dyadicTentSum_tail J n
    have he : ((2 : ℝ)^J)^2 = 4^J := by
      rw [← pow_mul, Nat.mul_comm J 2,pow_mul]
      norm_num
    simp only [Coeff.exponentInclusion_apply,dyadicTentSumCoefficients_apply]
    rw [he]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) J]

/-- When the number of scales is 2P, the lp norm at exponent P remains uniformly bounded. -/
theorem norm_dyadicTentSumCoefficients_twice_exponent_le
    (P : ℕ) [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 3 ≤ P) :
    ‖Coeff.exponentInclusion (show (2 : ℝ≥0∞) ≤ P by exact_mod_cast (show 2 ≤ P by omega))
      (dyadicTentSumCoefficients (2*P))‖ ≤ 640 := by
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
  have h := norm_exponent_dyadicTentSumCoefficients_le
    (by simp : (P : ℝ≥0∞) ≠ ⊤)
    (show (2 : ℝ≥0∞) ≤ P by exact_mod_cast (show 2 ≤ P by omega)) (2*P)
  simp only [ENNReal.toReal_natCast] at h
  linarith

end NLS.Fourier
