import NLS.ZakharovShabat.ClassicalGradientFourierSummability
import NLS.ZakharovShabat.ClassicalSobolevRemainderSequenceBounds

/-! # G.5 for finite exponents

Both actual gradient errors have uniform outer ℓp majorants whenever
q > 1+1/p. In particular this applies to the conjugate exponent p′
for every finite p > 1, and hence to G.5's entire finite range.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual gradient-error Fourier norms are uniformly ℓp on every physical H¹ ball. -/
theorem exists_classicalEndpointGradient_fourier_uniform_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (M : ℝ) (hM : 0 ≤ M) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ), ‖v‖ ≤ 1 → ∀ (L : (ℂ × ℂ) →L[ℂ] ℂ), ‖L‖ ≤ 1 →
      ∀ (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ n : ℤ,
      ‖classicalEndpointGradientFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (classicalSobolevPotential a) (ν n) (ν n) v L P‖ ≤ b n := by
  obtain ⟨N,hN,hcut⟩ := exists_near_free_frequency_cutoff B hB
  apply exists_classicalGradient_fourier_uniform_memlp_of_time_bounds p hp q hq M
    (classicalGradientValueConstant M B) (classicalGradientDerivativeConstant M B)
    (classicalGradientValueConstant_nonneg M B hM) (classicalGradientDerivativeConstant_nonneg M B hM)
    ν ν (max N N₀) (lt_of_lt_of_le hN (le_max_left _ _))
  intro a ha v hv L hL n hn t
  obtain ⟨him,hz1,hzn⟩ := hcut n ((le_max_left N N₀).trans hn) (ν n)
    (hν n ((le_max_right N N₀).trans hn))
  have hnp : 0 < (n.natAbs : ℝ) := by exact_mod_cast lt_of_lt_of_le hN ((le_max_left N N₀).trans hn)
  have hzn' : (n.natAbs : ℝ) ≤ ‖ν n‖ := by nlinarith [Real.two_le_pi]
  have hz : ν n ≠ 0 := norm_pos_iff.mp (hnp.trans_le hzn')
  refine ⟨?_,norm_deriv_classicalEndpointGradientRemainder_sobolev_strip_le M B a ha (ν n) hz him v hv L hL t⟩
  exact (norm_classicalEndpointGradientRemainder_sobolev_strip_le M B a ha (ν n) hz him v hv L hL t).trans
    (div_le_div_of_nonneg_left (classicalGradientValueConstant_nonneg M B hM) hnp hzn')

/-- The shifted-free gradient error has the same uniform summability under inverse-index displacement. -/
theorem exists_classicalEndpointGradient_shifted_fourier_uniform_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (M : ℝ) (hM : 0 ≤ M) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ)) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ), ‖v‖ ≤ 1 → ∀ (L : (ℂ × ℂ) →L[ℂ] ℂ), ‖L‖ ≤ 1 →
      ∀ (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ n : ℤ,
      ‖classicalEndpointGradientFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (classicalSobolevPotential a) (ν n) ((Real.pi*(n : ℝ) : ℝ) : ℂ) v L P‖ ≤ b n := by
  obtain ⟨N,hN⟩ := exists_nat_gt B
  have hNp : 0 < N := by exact_mod_cast lt_of_le_of_lt hB hN
  apply exists_classicalGradient_fourier_uniform_memlp_of_time_bounds p hp q hq M
    (classicalGradientShiftedValueConstant M B) (classicalGradientShiftedDerivativeConstant M B)
    (classicalGradientShiftedValueConstant_nonneg M B hM hB)
    (classicalGradientShiftedDerivativeConstant_nonneg M B hM hB)
    ν (fun n => ((Real.pi*(n : ℝ) : ℝ) : ℂ)) (max N N₀) (lt_of_lt_of_le hNp (le_max_left _ _))
  intro a ha v hv L hL n hn t
  have hnN := (le_max_left N N₀).trans hn
  have hn1 : 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast lt_of_lt_of_le hNp hnN
  have hBn : B ≤ (n.natAbs : ℝ) := hN.le.trans (by exact_mod_cast hnN)
  have hδ : ‖ν n-((Real.pi*(n : ℝ) : ℝ) : ℂ)‖ ≤ B/(n.natAbs : ℝ) := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using hν n ((le_max_right N N₀).trans hn)
  exact ⟨norm_classicalEndpointGradientRemainder_shifted_le M B hB a ha n hn1 hBn (ν n) hδ v hv L hL t,
    norm_deriv_classicalEndpointGradientRemainder_shifted_le M B hB a ha n hn1 hBn (ν n) hδ v hv L hL t⟩

/-- The conjugate exponent is strictly above the summability threshold for every finite p>1. -/
theorem conjugate_exponent_gt_gradient_threshold (p : ℝ) (hp : 1 < p) :
    1+1/p < p/(p-1) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p-1 := by linarith
  apply (lt_div_iff₀ hpm).mpr
  have hdiv : (1/p)*p = 1 := div_mul_cancel₀ 1 hp0.ne'
  have hpos : 0 < 1/p := by positivity
  nlinarith

theorem conjugate_exponent_ennreal_gt_gradient_threshold (p : ℝ) (hp : 1 < p) :
    ENNReal.ofReal (1+1/p) < ENNReal.ofReal (p/(p-1)) :=
  (ENNReal.ofReal_lt_ofReal_iff (div_pos (by linarith) (by linarith))).mpr
    (conjugate_exponent_gt_gradient_threshold p hp)

/-- The actual Fourier norms belong to outer ℓp at every target exponent above the threshold. -/
theorem memlp_classicalEndpointGradient_fourier_norms
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1)
    (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1) (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalEndpointGradientFourierCoefficients (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential a) (ν n) (ν n) v L P‖) (ENNReal.ofReal p) := by
  let : Fact (1 ≤ q) := ⟨(ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))).trans hq.le⟩
  obtain ⟨b,hb,h⟩ := exists_classicalEndpointGradient_fourier_uniform_memlp p hp q hq
    ‖a‖ (norm_nonneg a) B hB N₀ ν hν
  apply hb.mono
  intro n
  simpa only [norm_norm] using h a le_rfl v hv L hL P hP n

/-- G.5's conjugate-exponent summability for every finite p>1. -/
theorem memlp_classicalEndpointGradient_conjugate_fourier_norms
    (p : ℝ) (hp : 1 < p) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1)
    (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1) (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalEndpointGradientFourierCoefficients (q := ENNReal.ofReal (p/(p-1)))
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
        (conjugate_exponent_ennreal_gt_gradient_threshold p hp))
      (classicalSobolevPotential a) (ν n) (ν n) v L P‖) (ENNReal.ofReal p) :=
  memlp_classicalEndpointGradient_fourier_norms p hp _ (conjugate_exponent_ennreal_gt_gradient_threshold p hp)
    B hB N₀ ν hν a v hv L hL P hP

/-- The actual Fourier norms belong to outer ℓp at every target exponent above the threshold. -/
theorem memlp_classicalEndpointGradient_shifted_fourier_norms
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1)
    (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1) (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalEndpointGradientFourierCoefficients (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential a) (ν n) ((Real.pi*(n : ℝ) : ℝ) : ℂ) v L P‖) (ENNReal.ofReal p) := by
  let : Fact (1 ≤ q) := ⟨(ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))).trans hq.le⟩
  obtain ⟨b,hb,h⟩ := exists_classicalEndpointGradient_shifted_fourier_uniform_memlp p hp q hq
    ‖a‖ (norm_nonneg a) B hB N₀ ν hν
  apply hb.mono
  intro n
  simpa only [norm_norm] using h a le_rfl v hv L hL P hP n

/-- G.5's conjugate-exponent summability for every finite p>1. -/
theorem memlp_classicalEndpointGradient_shifted_conjugate_fourier_norms
    (p : ℝ) (hp : 1 < p) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1)
    (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1) (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalEndpointGradientFourierCoefficients (q := ENNReal.ofReal (p/(p-1)))
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
        (conjugate_exponent_ennreal_gt_gradient_threshold p hp))
      (classicalSobolevPotential a) (ν n) ((Real.pi*(n : ℝ) : ℝ) : ℂ) v L P‖) (ENNReal.ofReal p) :=
  memlp_classicalEndpointGradient_shifted_fourier_norms p hp _ (conjugate_exponent_ennreal_gt_gradient_threshold p hp)
    B hB N₀ ν hν a v hv L hL P hP

end NLS.ZakharovShabat
