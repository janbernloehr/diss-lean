import NLS.KdV.HillCanonicalGapBounds
import NLS.SequenceSpaces.QuadraticSeparationTail
import NLS.SequenceSpaces.WeightedSquareSums
import NLS.SequenceSpaces.WeightedCutoffPowers

/-! # Weighted high Hill critical-product tails with the corrected gap remainder. -/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
open Metric Complex
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillPeriodOne_critical_log_tail_bound (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) (N n : ℕ) (hN : 2≤N) (hn : N≤n)
    (hcut : 8*‖q‖ ≤ (N : ℝ)) (W : ℝ) (hW : 0<W)
    (hw : ∀ k : ℕ, W ≤ w (2*((k+N : ℕ) : ℤ))) :
    Summable (fun k : ℕ => hillPeriodOneGap w q hr (k+N)/
      (4*|((k+N : ℕ) : ℝ)^2-(n : ℝ)^2|)) ∧
      (∑' k : ℕ, hillPeriodOneGap w q hr (k+N)/
        (4*|((k+N : ℕ) : ℝ)^2-(n : ℝ)^2|))^2 ≤
      (9*‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)‖^2+
        2304*‖q‖^4/(N : ℝ))/(16*(N : ℝ)^2*W^2) := by
  obtain ⟨hs,ht⟩ := hillPeriodOne_canonical_gap_tail_bound w q hr N hN hcut
  obtain ⟨hgs,hgt⟩ := NLS.SequenceSpaces.square_sum_le_of_weight_lower_bound
    (fun k : ℕ => w (2*((k+N : ℕ) : ℤ)))
    (fun k : ℕ => hillPeriodOneGap w q hr (k+N)) W hW hw hs
  obtain ⟨hls,hlt⟩ := NLS.SequenceSpaces.quadratic_separation_cauchy_schwarz
    (fun k : ℕ => hillPeriodOneGap w q hr (k+N)) N n (by omega) hn
    (fun k => hillPeriodOneGap_nonneg w q hr (k+N)) hgs
  refine ⟨hls,?_⟩
  calc
    _ ≤ (∑' k : ℕ, hillPeriodOneGap w q hr (k+N)^2)/(16*(N : ℝ)^2) := hlt
    _ ≤ ((∑' k : ℕ, (w (2*((k+N : ℕ) : ℤ)))^2*hillPeriodOneGap w q hr (k+N)^2)/W^2)/(16*(N : ℝ)^2) :=
      div_le_div_of_nonneg_right hgt (by positivity)
    _ ≤ ((9*‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)‖^2+
        2304*‖q‖^4/(N : ℝ))/W^2)/(16*(N : ℝ)^2) :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right ht (sq_nonneg W)) (by positivity)
    _ = _ := by ring

theorem hillPeriodOne_critical_log_tail_le_one (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) (N n : ℕ) (hN : 2≤N) (hn : N≤n)
    (Q r : ℝ) (hQ : 1≤Q) (hqQ : ‖q‖≤Q) (hr0 : 0≤r) (hr1 : r≤1/2)
    (hcut : 8*Q^(3/2-r) ≤ (N : ℝ))
    (hw : ∀ k : ℕ, (N : ℝ)^r ≤ w (2*((k+N : ℕ) : ℤ))) :
    Summable (fun k : ℕ => hillPeriodOneGap w q hr (k+N)/
      (4*|((k+N : ℕ) : ℝ)^2-(n : ℝ)^2|)) ∧
      (∑' k : ℕ, hillPeriodOneGap w q hr (k+N)/
        (4*|((k+N : ℕ) : ℝ)^2-(n : ℝ)^2|)) ≤ 1 := by
  have hNpos : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hQpow : Q≤Q^(3/2-r) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ (by linarith : 1≤3/2-r)
  have hcutq : 8*‖q‖≤(N : ℝ) := by linarith
  obtain ⟨hs,ht⟩ := hillPeriodOne_critical_log_tail_bound w q hr N n hN hn hcutq
    ((N : ℝ)^r) (Real.rpow_pos_of_pos hNpos _) hw
  have hfn : ‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)‖ ≤ Q := by
    have hh := Coeff.norm_fourierTail_le (by norm_num : (2 : ENNReal)≠0) N
      (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)
    rw [← WeightedCoeff.norm_eq] at hh
    exact hh.trans hqQ
  have hfsq : ‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)‖^2≤Q^2 := by
    nlinarith [norm_nonneg (Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q))]
  have hq4 : ‖q‖^4≤Q^4 := pow_le_pow_left₀ (norm_nonneg q) hqQ 4
  have hR : (9*‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)‖^2+
      2304*‖q‖^4/(N : ℝ))/(16*(N : ℝ)^2*((N : ℝ)^r)^2) ≤ 1 := by
    apply le_trans ?_ (NLS.SequenceSpaces.corrected_weighted_gap_tail_exponent_le_one Q N r hQ hr0 hr1 hcut)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left hfsq (by norm_num))
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq4 (by norm_num)) hNpos.le)
  refine ⟨hs,?_⟩
  have hh := ht.trans hR
  nlinarith

end NLS.KdV
