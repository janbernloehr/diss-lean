import NLS.Fourier.UnitIntervalC1FourierLebesgue
import NLS.ZakharovShabat.ClassicalSobolevRemainderSequenceBounds

/-! # Uniform Fourier–Lebesgue endpoint bounds for the actual remainder

The actual time derivative gives a common inverse-bracket coefficient
majorant. This supplies the uniform ℓq endpoint needed in G.3 for every
q > 1, without changing the Fourier coefficients used at q = 2.
-/

noncomputable section
open Set NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {q : ℝ≥0∞}

/-- The actual unit-interval Fourier sequence at any exponent above one. -/
def classicalSobolevRemainderFourierCoefficients (hq : 1 < q)
    (a : ScalarDomain 2 × ScalarDomain 2) (z : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) : Coeff q :=
  unitIntervalC1Coefficients hq
    (fun t => L (classicalSolutionRemainder (classicalSobolevPotential a) z v t))
    (contDiff_classicalRemainder_observation _ z v L)

@[simp] theorem classicalSobolevRemainderFourierCoefficients_apply (hq : 1 < q)
    (a : ScalarDomain 2 × ScalarDomain 2) (z : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) (n : ℤ) :
    classicalSobolevRemainderFourierCoefficients hq a z v L n =
      intervalFourierCoefficient 1 (fun t => L (classicalSolutionRemainder (classicalSobolevPotential a) z v t)) n := rfl

/-- The new Fourier–Lebesgue sequence is exactly the existing Parseval sequence at exponent two. -/
theorem classicalSobolevRemainderFourierCoefficients_two
    (a : ScalarDomain 2 × ScalarDomain 2) (z : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) :
    classicalSobolevRemainderFourierCoefficients (q := 2) (by norm_num) a z v L =
      classicalSobolevRemainderL2Coefficients a z v L := by ext n; rfl

/-- Uniform Fourier–Lebesgue control on each H¹ ball and spectral strip, for every q > 1. -/
theorem norm_classicalSobolevRemainderFourierCoefficients_le [Fact (1 ≤ q)] (hq : 1 < q)
    (M H : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (z : ℂ) (hz : z ≠ 0) (hH : |z.im| ≤ H) (hz1 : 1 ≤ ‖z‖)
    (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) (hL : ‖L‖ ≤ 1) :
    ‖classicalSobolevRemainderFourierCoefficients hq a z v L‖ ≤
      (2*classicalSobolevErrorConstant M H+classicalSobolevDerivativeConstant M H)*‖v‖*
        unitIntervalC1FourierConstant hq := by
  have hC := classicalSobolevErrorConstant_nonneg M H ((norm_nonneg a).trans ha)
  have hD := classicalSobolevDerivativeConstant_nonneg M H ((norm_nonneg a).trans ha)
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖L (classicalSolutionRemainder (classicalSobolevPotential a) z v t)‖ ≤
        classicalSobolevErrorConstant M H*‖v‖ :=
    (norm_classicalSobolevRemainder_observation_le M H a ha z hz hH v L hL ⟨t,ht⟩).trans
      (div_le_self (mul_nonneg hC (norm_nonneg _)) hz1)
  have h := norm_unitIntervalC1Coefficients_le hq _ (contDiff_classicalRemainder_observation _ z v L)
    (classicalSobolevErrorConstant M H*‖v‖) (classicalSobolevDerivativeConstant M H*‖v‖)
    (mul_nonneg hC (norm_nonneg _)) (mul_nonneg hD (norm_nonneg _)) hf
    (fun t ht => norm_deriv_classicalSobolevRemainder_observation_le M H a ha z hz hH v L hL ⟨t,ht⟩)
  exact h.trans_eq (by ring)

/-- Bounded displacement from nπ gives one uniform Fourier–Lebesgue bound beyond a common cutoff. -/
theorem exists_classicalSobolevRemainder_sequence_fourier_bound [Fact (1 ≤ q)] (hq : 1 < q)
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ν : ℤ → ℂ),
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ), ‖L‖ ≤ 1 →
      ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalSobolevRemainderFourierCoefficients hq a (ν n) v L‖ ≤
        (2*classicalSobolevErrorConstant M B+classicalSobolevDerivativeConstant M B)*‖v‖*
          unitIntervalC1FourierConstant hq := by
  obtain ⟨N,hN,hcut⟩ := exists_near_free_frequency_cutoff B hB
  refine ⟨max N N₀,lt_of_lt_of_le hN (le_max_left _ _),?_⟩
  intro ν hν a ha v L hL n hn
  obtain ⟨him,hz1,_⟩ := hcut n ((le_max_left N N₀).trans hn) (ν n)
    (hν n ((le_max_right N N₀).trans hn))
  have hz : ν n ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hz1)
  exact norm_classicalSobolevRemainderFourierCoefficients_le hq M B a ha (ν n) hz him hz1 v L hL

end NLS.ZakharovShabat
