import NLS.Fourier.ArbitraryPeriodDistribution
import NLS.SequenceSpaces.TemperedWeight

/-! # Polynomial coefficient synthesis on every positive period

Raw polynomially bounded coefficients, including an unrestricted zero mode,
produce one unique actual periodic tempered distribution.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal SchwartzMap
namespace NLS.Fourier

/-- Polynomially growing raw data have a unique actual periodic distribution on any positive period. -/
theorem existsUnique_periodicDistribution_of_polynomial_bound
    (L : ℝ) (hL : 0 < L) (α : ℤ → ℂ) (N : ℕ) (C : ℝ)
    (hα : ∀ n : ℤ, ‖α n‖ ≤ C*(1+|(n:ℝ)|)^N) :
    ∃! T : 𝓢'(ℝ,ℂ), IsPeriodicDistribution L T ∧ ∀ n : ℤ, T (periodCoefficientTest L hL n) = α n := by
  let w := Weight.sobolev (-(N:ℝ))
  have hmem : Memℓp (fun n : ℤ => (w n:ℂ)*α n) ⊤ := by
    apply memℓp_infty
    refine ⟨C,?_⟩
    rintro _ ⟨n,rfl⟩
    change ‖(w n:ℂ)*α n‖ ≤ C
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (w.positive n).le]
    change (1+|(n:ℝ)|)^(-(N:ℝ))*‖α n‖ ≤ C
    rw [Real.rpow_neg (by positivity),Real.rpow_natCast]
    calc
      _ ≤ ((1+|(n:ℝ)|)^N)⁻¹*(C*(1+|(n:ℝ)|)^N) := by gcongr; exact hα n
      _ = C := by field_simp
  let a : WeightedCoeff w ⊤ := ⟨α,hmem⟩
  let T := arbitraryPeriodDistributionSynthesis L hL w (Weight.hasTemperedInverse_sobolev _) a
  have hT : IsPeriodicDistribution L T := arbitraryPeriodDistributionSynthesis_periodic L hL w _ a
  have hc (n : ℤ) : T (periodCoefficientTest L hL n) = α n :=
    arbitraryPeriodDistributionSynthesis_coefficient L hL w _ a n
  refine ⟨T,⟨hT,hc⟩,?_⟩
  intro U hU
  exact periodicDistribution_ext_arbitraryPeriod L hL hU.1 hT (fun n => (hU.2 n).trans (hc n).symm)

/-- The source's asymptotic growth hypothesis, with no restriction on the zero mode. -/
theorem existsUnique_periodicDistribution_of_polynomial_isBigO
    (L : ℝ) (hL : 0 < L) (α : ℤ → ℂ) (N : ℕ)
    (hα : Asymptotics.IsBigO Filter.cofinite α (fun n : ℤ => |(n:ℝ)|^N)) :
    ∃! T : 𝓢'(ℝ,ℂ), IsPeriodicDistribution L T ∧ ∀ n : ℤ, T (periodCoefficientTest L hL n) = α n := by
  obtain ⟨C,hC,hb⟩ := Asymptotics.bound_of_isBigO_cofinite hα
  apply existsUnique_periodicDistribution_of_polynomial_bound L hL α N (C+‖α 0‖)
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [Int.cast_zero,abs_zero,add_zero,one_pow,mul_one]
    linarith
  · have habs : 0 < |(n:ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    have h := hb (pow_ne_zero N habs.ne')
    rw [Real.norm_of_nonneg (pow_nonneg habs.le _)] at h
    have hp : |(n:ℝ)|^N ≤ (1+|(n:ℝ)|)^N := pow_le_pow_left₀ habs.le (by linarith) N
    calc
      _ ≤ C*|(n:ℝ)|^N := h
      _ ≤ (C+‖α 0‖)*(1+|(n:ℝ)|)^N := by gcongr; exact le_add_of_nonneg_right (norm_nonneg _)


end NLS.Fourier
