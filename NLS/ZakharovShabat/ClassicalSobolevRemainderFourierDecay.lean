import NLS.ZakharovShabat.ClassicalSobolevRemainderInterpolation

/-! # Appendix G.3 decay along near-free spectral sequences

A bounded displacement from nπ turns the spectral-frequency bound into
the stated inverse-index power, uniformly on each Sobolev ball and
under one common displacement bound. The shifted-free comparison is
separate and is not asserted here.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The Fourier–Lebesgue decay in G.3, with the displayed exponent and uniform cutoff.
The finite initial portion of a spectral sequence is unrestricted. -/
theorem exists_classicalSobolevRemainder_sequence_fourier_decay
    (ε q : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hq0 : 1+ε ≤ q) (hq2 : q ≤ 2)
    [Fact (1 ≤ ENNReal.ofReal q)] (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ν : ℤ → ℂ),
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ), ‖L‖ ≤ 1 →
      ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalSobolevRemainderFourierCoefficients (q := ENNReal.ofReal q)
        (ENNReal.one_lt_ofReal.mpr (by linarith)) a (ν n) v L‖ ≤
        classicalSobolevInterpolationConstant ε hε M B*‖v‖/
          (n.natAbs : ℝ)^(fundamentalFourierDecayExponent ε q) := by
  obtain ⟨N,hN,hcut⟩ := exists_near_free_frequency_cutoff B hB
  refine ⟨max N N₀,lt_of_lt_of_le hN (le_max_left _ _),?_⟩
  intro ν hν a ha v L hL n hn
  have hnN := (le_max_left N N₀).trans hn
  obtain ⟨him,hz1,hzn⟩ := hcut n hnN (ν n) (hν n ((le_max_right N N₀).trans hn))
  have hz : ν n ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hz1)
  have hnpos : 0 < (n.natAbs : ℝ) := by exact_mod_cast lt_of_lt_of_le hN hnN
  have hzn' : (n.natAbs : ℝ) ≤ ‖ν n‖ := by nlinarith [Real.two_le_pi]
  apply (norm_classicalSobolevRemainderFourierCoefficients_interpolate ε q hε hε1 hq0 hq2
    M B a ha (ν n) hz him hz1 v L hL).trans
  exact div_le_div_of_nonneg_left
    (mul_nonneg (classicalSobolevInterpolationConstant_nonneg ε hε M B ((norm_nonneg a).trans ha))
      (norm_nonneg _)) (Real.rpow_pos_of_pos hnpos _)
    (Real.rpow_le_rpow hnpos.le hzn' (fundamentalFourierDecayExponent_nonneg hε1 hq0))

end NLS.ZakharovShabat
