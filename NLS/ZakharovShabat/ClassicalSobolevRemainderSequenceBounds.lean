import NLS.ZakharovShabat.ClassicalSobolevRemainderTimeBounds

/-! # The L² and H¹ endpoints of Appendix G.3 along near-free sequences

A bounded displacement from `nπ` gives a common horizontal strip and a
uniform lower bound proportional to `|n|` beyond one cutoff. The estimates
are uniform over the whole potential ball and all such spectral sequences.
-/

noncomputable section
open Set Complex NLS.Fourier
namespace NLS.ZakharovShabat

/-- Bounded displacement from the free lattice gives strip and frequency bounds at one cutoff. -/
theorem exists_near_free_frequency_cutoff (B : ℝ) (hB : 0 ≤ B) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ,
      ‖z-(Real.pi : ℂ)*n‖ ≤ B →
      |z.im| ≤ B ∧ 1 ≤ ‖z‖ ∧ Real.pi*(n.natAbs : ℝ)/2 ≤ ‖z‖ := by
  obtain ⟨N,hN⟩ := exists_nat_gt (2*(B+1)/Real.pi)
  have hNπ : 2*(B+1) < Real.pi*(N : ℝ) := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hN
    nlinarith
  have hNpos : 0 < N := by
    by_contra hn
    have : N = 0 := by omega
    simp only [this,Nat.cast_zero,mul_zero] at hNπ
    linarith
  refine ⟨N,hNpos,fun n hn z hz => ?_⟩
  have hn' : (N : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hn
  have hnorm : ‖(Real.pi : ℂ)*n‖ = Real.pi*(n.natAbs : ℝ) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
      Complex.norm_intCast,Nat.cast_natAbs,Int.cast_abs]
  have ht := norm_sub_norm_le ((Real.pi : ℂ)*n) z
  rw [norm_sub_rev,hnorm] at ht
  have him : |z.im| ≤ B := by
    have h := (Complex.abs_im_le_norm (z-(Real.pi : ℂ)*n)).trans hz
    simpa using h
  refine ⟨him,?_,?_⟩ <;> nlinarith [Real.pi_pos]

/-- A single cutoff gives the `O(1/|n|)` Fourier ℓ² and `O(1)` H¹ time bounds of G.3.
The sequence displacement may only be controlled outside an initial finite set. -/
theorem exists_classicalSobolevRemainder_sequence_time_bounds
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ν : ℤ → ℂ),
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ), ‖L‖ ≤ 1 →
      ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalSobolevRemainderL2Coefficients a (ν n) v L‖ ≤
        (2*classicalSobolevErrorConstant M B*‖v‖/Real.pi)/(n.natAbs : ℝ) ∧
      Real.sqrt (intervalH1Energy
        (fun t => L (classicalSolutionRemainder (classicalSobolevPotential a) (ν n) v t)) 0 1) ≤
        (classicalSobolevErrorConstant M B+classicalSobolevDerivativeConstant M B)*‖v‖ := by
  obtain ⟨N,hN,hcut⟩ := exists_near_free_frequency_cutoff B hB
  refine ⟨max N N₀,lt_of_lt_of_le hN (le_max_left _ _),?_⟩
  intro ν hν a ha v L hL n hn
  have hnN := (le_max_left N N₀).trans hn
  obtain ⟨him,hz1,hzn⟩ := hcut n hnN (ν n) (hν n ((le_max_right N N₀).trans hn))
  have hz : ν n ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hz1)
  have hnpos : 0 < (n.natAbs : ℝ) := by exact_mod_cast lt_of_lt_of_le hN hnN
  constructor
  · apply (norm_classicalSobolevRemainderL2Coefficients_le M B a ha (ν n) hz him v L hL).trans
    calc
      _ ≤ classicalSobolevErrorConstant M B*‖v‖/(Real.pi*(n.natAbs : ℝ)/2) :=
        div_le_div_of_nonneg_left
          (mul_nonneg (classicalSobolevErrorConstant_nonneg M B ((norm_nonneg a).trans ha)) (norm_nonneg _))
          (by positivity) hzn
      _ = _ := by ring
  · exact sqrt_intervalH1Energy_classicalSobolevRemainder_le M B a ha (ν n) hz him v L hL hz1

end NLS.ZakharovShabat
