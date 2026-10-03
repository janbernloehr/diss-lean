import NLS.ZakharovShabat.ClassicalEndpointGradientL2
import NLS.ZakharovShabat.ClassicalSobolevRemainderSequenceBounds
import NLS.SequenceSpaces.PowerDecaySummability

/-! # The Hilbert case of G.5

For both free-reference choices, the actual gradient-error Fourier norms
have a common ℓ² majorant on every physical H¹ coefficient ball.
The finite spectral head is included, without excluding zero frequency.
-/

noncomputable section
namespace NLS.ZakharovShabat

private theorem gradientL2_uniform_memlp_of_tail
    (M K : ℝ) (N : ℕ) (ν ω : ℤ → ℂ)
    (h : ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ), ‖v‖ ≤ 1 → ∀ (L : (ℂ × ℂ) →L[ℂ] ℂ), ‖L‖ ≤ 1 →
      ∀ (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalEndpointGradientRemainderL2Coefficients (classicalSobolevPotential a) (ν n) (ω n) v L P‖ ≤
        K/(n.natAbs : ℝ)) :
    ∃ b : ℤ → ℝ, Memℓp b 2 ∧ ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ), ‖v‖ ≤ 1 → ∀ (L : (ℂ × ℂ) →L[ℂ] ℂ), ‖L‖ ≤ 1 →
      ∀ (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ n : ℤ,
      ‖classicalEndpointGradientRemainderL2Coefficients (classicalSobolevPotential a) (ν n) (ω n) v L P‖ ≤ b n := by
  let g (n : ℤ) := K*(n.natAbs : ℝ)^(-(1 : ℝ))
  have hg : Memℓp g (ENNReal.ofReal (2 : ℝ)) :=
    (memlp_inverse_natAbs_rpow 2 (by norm_num) 1 (by norm_num)).const_mul K
  let b (n : ℤ) := if N ≤ n.natAbs then ‖g n‖ else 12*(Real.exp (4*M+‖ν n‖+‖ω n‖))^3
  refine ⟨b,?_,?_⟩
  · have hb := memlp_of_natAbs_eventual_bound 2 (by norm_num) b (fun n => ‖g n‖) hg.norm N
      (by intro n hn; simp [b,hn])
    simpa using hb
  intro a ha v hv L hL P hP n
  by_cases hn : N ≤ n.natAbs
  · calc
      _ ≤ K/(n.natAbs : ℝ) := h a ha v hv L hL P hP n hn
      _ = g n := by simp [g,Real.rpow_neg_one,div_eq_mul_inv]
      _ ≤ b n := by simp only [b,if_pos hn]; exact Real.le_norm_self _
  · simpa only [b,if_neg hn] using
      norm_classicalEndpointGradientRemainderL2Coefficients_all_frequencies_le M a ha (ν n) (ω n) v hv L hL P hP

/-- G.5 at p=2, with the free reference at the original spectral frequency. -/
theorem exists_classicalEndpointGradient_fourier_uniform_memlp_two
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) :
    ∃ b : ℤ → ℝ, Memℓp b 2 ∧ ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ), ‖v‖ ≤ 1 → ∀ (L : (ℂ × ℂ) →L[ℂ] ℂ), ‖L‖ ≤ 1 →
      ∀ (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ n : ℤ,
      ‖classicalEndpointGradientRemainderL2Coefficients (classicalSobolevPotential a) (ν n) (ν n) v L P‖ ≤ b n := by
  obtain ⟨N,hN,hcut⟩ := exists_near_free_frequency_cutoff B hB
  apply gradientL2_uniform_memlp_of_tail M
    (6*(Real.exp (4*M+B))^2*classicalSobolevErrorConstant M B) (max N N₀) ν ν
  intro a ha v hv L hL P hP n hn
  obtain ⟨him,hz1,hzn⟩ := hcut n ((le_max_left N N₀).trans hn) (ν n)
    (hν n ((le_max_right N N₀).trans hn))
  have hnp : 0 < (n.natAbs : ℝ) := by exact_mod_cast lt_of_lt_of_le hN ((le_max_left N N₀).trans hn)
  have hzn' : (n.natAbs : ℝ) ≤ ‖ν n‖ := by nlinarith [Real.two_le_pi]
  have hz : ν n ≠ 0 := norm_pos_iff.mp (hnp.trans_le hzn')
  have hC := classicalSobolevErrorConstant_nonneg M B ((norm_nonneg a).trans ha)
  exact (norm_classicalEndpointGradientRemainderL2Coefficients_sobolev_le M B a ha (ν n) hz him v hv L hL P hP).trans
    (div_le_div_of_nonneg_left (by positivity) hnp hzn')

/-- G.5 at p=2, with free reference at nπ under inverse-index displacement. -/
theorem exists_classicalEndpointGradient_shifted_fourier_uniform_memlp_two
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ)) :
    ∃ b : ℤ → ℝ, Memℓp b 2 ∧ ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ), ‖v‖ ≤ 1 → ∀ (L : (ℂ × ℂ) →L[ℂ] ℂ), ‖L‖ ≤ 1 →
      ∀ (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ n : ℤ,
      ‖classicalEndpointGradientRemainderL2Coefficients (classicalSobolevPotential a) (ν n)
        ((Real.pi*(n : ℝ) : ℝ) : ℂ) v L P‖ ≤ b n := by
  obtain ⟨N,hN⟩ := exists_nat_gt B
  have hNp : 0 < N := by exact_mod_cast lt_of_le_of_lt hB hN
  apply gradientL2_uniform_memlp_of_tail M
    (6*(Real.exp (4*M+B))^2*(classicalSobolevErrorConstant M B+2*B)) (max N N₀) ν
    (fun n => ((Real.pi*(n : ℝ) : ℝ) : ℂ))
  intro a ha v hv L hL P hP n hn
  have hnN := (le_max_left N N₀).trans hn
  have hn1 : 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast lt_of_lt_of_le hNp hnN
  have hBn : B ≤ (n.natAbs : ℝ) := hN.le.trans (by exact_mod_cast hnN)
  apply norm_classicalEndpointGradientRemainderL2Coefficients_shifted_le M B hB a ha n hn1 hBn
    (ν n) _ v hv L hL P hP
  simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using hν n ((le_max_right N N₀).trans hn)

/-- The actual gradient-error Fourier norms form an ℓ² sequence. -/
theorem memlp_classicalEndpointGradient_fourier_norms_two
    (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1)
    (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1) (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalEndpointGradientRemainderL2Coefficients
      (classicalSobolevPotential a) (ν n) (ν n) v L P‖) 2 := by
  obtain ⟨b,hb,h⟩ := exists_classicalEndpointGradient_fourier_uniform_memlp_two ‖a‖ B hB N₀ ν hν
  apply hb.mono
  intro n
  simpa only [norm_norm] using h a le_rfl v hv L hL P hP n

/-- The actual gradient-error Fourier norms form an ℓ² sequence. -/
theorem memlp_classicalEndpointGradient_shifted_fourier_norms_two
    (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1)
    (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1) (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalEndpointGradientRemainderL2Coefficients
      (classicalSobolevPotential a) (ν n) ((Real.pi*(n : ℝ) : ℝ) : ℂ) v L P‖) 2 := by
  obtain ⟨b,hb,h⟩ := exists_classicalEndpointGradient_shifted_fourier_uniform_memlp_two ‖a‖ B hB N₀ ν hν
  apply hb.mono
  intro n
  simpa only [norm_norm] using h a le_rfl v hv L hL P hP n

end NLS.ZakharovShabat
