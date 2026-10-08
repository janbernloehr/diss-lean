import NLS.ZakharovShabat.SourceRelativeHigherActions
import NLS.ZakharovShabat.SourceH1HigherActionEstimates
import NLS.ZakharovShabat.SourceWeightedActionMajorant

/-! # Central comparisons with level-three actions in Lemma 27.2 -/
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- The central region includes index zero even when the potential is small. -/
theorem H1_gap_point_central_or_zero_bound
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : n = 0 ∨ 1+|(n:ℝ)| < 8*‖φ‖^2) (ζ : ℝ)
    (hζ : ζ ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair _ φ) heven n).re
      (canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair _ φ) heven n).re) :
    |ζ| ≤ 8*Real.pi*(1+‖φ‖^2) := by
  by_cases hl : 1+|(n:ℝ)| < 8*‖φ‖^2
  · have h := H1_gap_point_central_bound φ heven n hl ζ hζ
    nlinarith [Real.pi_pos]
  have hn0 : n = 0 := hn.resolve_right hl
  subst n
  have hh := H1_gap_point_localization φ heven 0 (le_of_not_gt hl) ζ hζ
  have hr := quadraticLocalizationRadius_le (norm_nonneg φ) 0 (le_of_not_gt hl)
  simp only [Int.cast_zero,mul_zero,sub_zero] at hh
  have hp : 0 ≤ Real.pi*‖φ‖^2 := by positivity
  nlinarith [Real.pi_gt_three]

/-- The source central estimate with the level-three action, including m=1. -/
theorem sourceRealHigherAction_H1_central_le_third (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (n : ℤ) (hn : n = 0 ∨ 1+|(n:ℝ)| < 8*‖φ‖^2) (m : ℕ) (hm : 1 ≤ m) :
    4^m*sourceRealHigherAction (by simp) (by norm_num) ψ n (2*m) ≤
      (16*Real.pi)^(2*(m-1))*(1+‖φ‖^2)^(2*(m-1))*
        (4*sourceRealHigherAction (by simp) (by norm_num) ψ n 2) := by
  have heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0 :=
    hφ ▸ periodOnePotential_mem ψ.val
  have h := sourceRealHigherAction_even_level_le (by simp) (by norm_num) ψ n 1 (m-1)
    (8*Real.pi*(1+‖φ‖^2)) (fun ζ hζ =>
      H1_gap_point_central_or_zero_bound φ heven n hn ζ (by simpa only [hφ] using hζ))
  rw [show 2*1+2*(m-1) = 2*m by omega] at h
  have hscale := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (4:ℝ)^m)
  have hp : (4:ℝ)^m = 4*2^(2*(m-1)) := by
    calc
      (4:ℝ)^m = 4^((m-1)+1) := congrArg (fun k => (4:ℝ)^k) (by omega)
      _ = 4*(2:ℝ)^(2*(m-1)) := by rw [pow_succ, pow_mul]; norm_num; ring
  calc
    _ ≤ 4^m*((8*Real.pi*(1+‖φ‖^2))^(2*(m-1))*
        sourceRealHigherAction (by simp) (by norm_num) ψ n (2*1)) := hscale
    _ = _ := by
      rw [hp]
      have hc : (2:ℝ)^(2*(m-1))*(8*Real.pi*(1+‖φ‖^2))^(2*(m-1)) =
          (16*Real.pi)^(2*(m-1))*(1+‖φ‖^2)^(2*(m-1)) := by
        rw [← mul_pow, show (2:ℝ)*(8*Real.pi*(1+‖φ‖^2)) = (16*Real.pi)*(1+‖φ‖^2) by ring, mul_pow]
      calc
        _ = 4*(2^(2*(m-1))*(8*Real.pi*(1+‖φ‖^2))^(2*(m-1)))*
          sourceRealHigherAction (by simp) (by norm_num) ψ n 2 := by ring
        _ = _ := by rw [hc]; ring

/-- A single nonnegative majorant combines the central third-level and exterior first-level bounds. -/
theorem sourceRealHigherAction_H1_le_action_add_third (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (n : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    4^m*sourceRealHigherAction (by simp) (by norm_num) ψ n (2*m) ≤
      sourceWeightedActionTerm ψ m n+
      (16*Real.pi)^(2*(m-1))*(1+‖φ‖^2)^(2*(m-1))*
        (4*sourceRealHigherAction (by simp) (by norm_num) ψ n 2) := by
  have hJ := sourceRealHigherAction_even_nonneg (by simp) (by norm_num) ψ n 1
  by_cases hn : n ≠ 0 ∧ 8*‖φ‖^2 ≤ 1+|(n:ℝ)|
  · have h := (sourceRealHigherAction_H1_exterior_bounds ψ φ hφ n hn.1 hn.2 m).2
    rw [← norm_sourceRealAction] at h
    exact h.trans (le_add_of_nonneg_right (by positivity))
  · have hc : n = 0 ∨ 1+|(n:ℝ)| < 8*‖φ‖^2 := by
      by_cases h0 : n = 0
      · exact Or.inl h0
      · exact Or.inr (lt_of_not_ge (fun h => hn ⟨h0,h⟩))
    exact (sourceRealHigherAction_H1_central_le_third ψ φ hφ n hc m hm).trans
      (le_add_of_nonneg_left (by unfold sourceWeightedActionTerm; positivity))

end NLS.ZakharovShabat
