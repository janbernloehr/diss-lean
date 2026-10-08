import NLS.ZakharovShabat.SourceHigherActionEstimates
import NLS.ZakharovShabat.H1GapIntervalLocalization
import NLS.ZakharovShabat.NonzeroQuadraticRadius

/-! # Proposition 26.1: quantitative higher-action estimates

The source's H¹ norm is the exact π-normalized weighted Hilbert norm of
its period-one physical realization. The higher-action index 2m denotes
the source level 2m+1. No division by an action or a gap is used, so every
statement includes collapsed gaps and level m=0.
-/
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- The mean-value point in Proposition 26.1 obeys the exact H¹ localization radius. -/
theorem sourceRealHigherAction_H1_meanValue_localization (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) (m : ℕ) :
    ∃ ζ ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n).re
      (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n).re,
      sourceRealHigherAction (by simp) (by norm_num) ψ n (2*m) =
        ζ^(2*m)*(sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re ∧
      |ζ-Real.pi*n| ≤ quadraticLocalizationRadius ‖φ‖ n := by
  obtain ⟨ζ,hζ,he⟩ := sourceRealHigherAction_eq_power_mul_action (by simp) (by norm_num) ψ n (2*m)
  refine ⟨ζ,hζ,he,?_⟩
  have heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0 :=
    hφ ▸ periodOnePotential_mem ψ.val
  exact H1_gap_point_localization φ heven n hn ζ (by simpa only [hφ] using hζ)

/-- The printed nonzero-index two-sided comparison, with every natural odd level. -/
theorem sourceRealHigherAction_H1_exterior_bounds (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (n : ℤ) (hn0 : n ≠ 0) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) (m : ℕ) :
    ((2:ℝ)⁻¹)^m*(1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*m)*
        (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re ≤
      4^m*sourceRealHigherAction (by simp) (by norm_num) ψ n (2*m) ∧
    4^m*sourceRealHigherAction (by simp) (by norm_num) ψ n (2*m) ≤
      (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*m)*
        (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re := by
  obtain ⟨ζ,_,he,hζ⟩ := sourceRealHigherAction_H1_meanValue_localization ψ φ hφ n hn m
  have hr := quadraticLocalizationRadius_le_three_eighths (norm_nonneg φ) n hn0 hn
  have hb := spectral_point_even_power_bounds n hn0 ζ (by linarith) m
  have hI := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp)
    (by norm_num) ψ.val ψ.property n).1
  rw [he]
  simpa only [mul_assoc] using And.intro
    (mul_le_mul_of_nonneg_right hb.1 hI) (mul_le_mul_of_nonneg_right hb.2 hI)

/-- The remaining low-index actions satisfy the printed central estimate. -/
theorem sourceRealHigherAction_H1_central_bound (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (n : ℤ) (hn : 1+|(n:ℝ)| < 8*‖φ‖^2) (m : ℕ) :
    4^m*|sourceRealHigherAction (by simp) (by norm_num) ψ n (2*m)| ≤
      (16*Real.pi)^(2*m)*‖φ‖^(4*m)*
        (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re := by
  obtain ⟨ζ,hζ,he⟩ := sourceRealHigherAction_eq_power_mul_action (by simp) (by norm_num) ψ n (2*m)
  have heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0 :=
    hφ ▸ periodOnePotential_mem ψ.val
  have hz := H1_gap_point_central_bound φ heven n hn ζ (by simpa only [hφ] using hζ)
  have hI := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp)
    (by norm_num) ψ.val ψ.property n).1
  have hp := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg ζ) hz (2*m)) hI)
    (by positivity : 0 ≤ (4:ℝ)^m)
  have hc : (4:ℝ)^m*(8*Real.pi*‖φ‖^2)^(2*m) = (16*Real.pi)^(2*m)*‖φ‖^(4*m) := by
    calc
      _ = ((2:ℝ)*(8*Real.pi*‖φ‖^2))^(2*m) := by
        rw [mul_pow (2:ℝ) (8*Real.pi*‖φ‖^2),pow_mul (2:ℝ)]
        norm_num
      _ = ((16*Real.pi)*‖φ‖^2)^(2*m) := by congr 1; ring
      _ = _ := by rw [mul_pow (16*Real.pi) (‖φ‖^2),← pow_mul]; congr 2; omega
  rw [abs_of_nonneg (sourceRealHigherAction_even_nonneg (by simp) (by norm_num) ψ n m),he,
    ← pow_abs_two_mul ζ]
  calc
    _ ≤ 4^m*((8*Real.pi*‖φ‖^2)^(2*m)*
        (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re) := hp
    _ = _ := by rw [← mul_assoc,hc]

end NLS.ZakharovShabat
