import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Power bounds at the norm-dependent weighted spectral cutoff. -/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.SequenceSpaces

theorem weighted_cutoff_denominator_lower (Q N r : ℝ) (hQ : 1≤Q) (hr0 : 0≤r) (hr1 : r≤1/2)
    (hN : 8*Q^(3/2-r) ≤ N) :
    64*Q^2 ≤ N^2*(N^r)^2 ∧ 512*Q^4 ≤ N^3*(N^r)^2 := by
  have hQ0 : 0≤Q := by linarith
  have hN0 : 0<N := (by positivity : 0<8*Q^(3/2-r)).trans_le hN
  have h2 : 2≤(3/2-r)*(2+2*r) := by nlinarith
  have h3 : 4≤(3/2-r)*(3+2*r) := by nlinarith
  have h8p2 : 64≤(8 : ℝ)^(2+2*r) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤8) (by linarith : 2≤2+2*r)
    norm_num at h
    exact h
  have h8p3 : 512≤(8 : ℝ)^(3+2*r) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤8) (by linarith : 3≤3+2*r)
    norm_num at h
    exact h
  have hQp2 : Q^2≤(Q^(3/2-r))^(2+2*r) := by
    rw [← Real.rpow_mul hQ0]
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hQ h2
  have hQp3 : Q^4≤(Q^(3/2-r))^(3+2*r) := by
    rw [← Real.rpow_mul hQ0]
    have h := Real.rpow_le_rpow_of_exponent_le hQ h3
    simpa only [show (4 : ℝ)=(4 : ℕ) by norm_num,Real.rpow_natCast] using h
  have hD2 : N^(2+2*r)=N^2*(N^r)^2 := by
    rw [Real.rpow_add hN0,Real.rpow_two,mul_comm (2 : ℝ) r,Real.rpow_mul hN0.le,Real.rpow_two]
  have hD3 : N^(3+2*r)=N^3*(N^r)^2 := by
    rw [Real.rpow_add hN0,show (3 : ℝ)=(3 : ℕ) by norm_num,Real.rpow_natCast]
    rw [mul_comm (2 : ℝ) r,Real.rpow_mul hN0.le,Real.rpow_two]
  constructor
  · calc
      _ ≤ (8 : ℝ)^(2+2*r)*(Q^(3/2-r))^(2+2*r) :=
        mul_le_mul h8p2 hQp2 (sq_nonneg Q) (Real.rpow_nonneg (by norm_num) _)
      _ = (8*Q^(3/2-r))^(2+2*r) := (Real.mul_rpow (by norm_num) (Real.rpow_nonneg hQ0 _)).symm
      _ ≤ N^(2+2*r) := Real.rpow_le_rpow (by positivity) hN (by linarith)
      _ = _ := hD2
  · calc
      _ ≤ (8 : ℝ)^(3+2*r)*(Q^(3/2-r))^(3+2*r) :=
        mul_le_mul h8p3 hQp3 (by positivity) (Real.rpow_nonneg (by norm_num) _)
      _ = (8*Q^(3/2-r))^(3+2*r) := (Real.mul_rpow (by norm_num) (Real.rpow_nonneg hQ0 _)).symm
      _ ≤ N^(3+2*r) := Real.rpow_le_rpow (by positivity) hN (by linarith)
      _ = _ := hD3

theorem corrected_weighted_gap_tail_exponent_le_one (Q N r : ℝ)
    (hQ : 1≤Q) (hr0 : 0≤r) (hr1 : r≤1/2) (hN : 8*Q^(3/2-r) ≤ N) :
    (9*Q^2+2304*Q^4/N)/(16*N^2*(N^r)^2) ≤ 1 := by
  have hN0 : 0<N := (by positivity : 0<8*Q^(3/2-r)).trans_le hN
  obtain ⟨hD2,hD3⟩ := weighted_cutoff_denominator_lower Q N r hQ hr0 hr1 hN
  have ht : 2304*Q^4/N ≤ 5*(N^2*(N^r)^2) := by
    apply (div_le_iff₀ hN0).mpr
    nlinarith [mul_nonneg (sq_nonneg N) (sq_nonneg (N^r))]
  apply (div_le_iff₀ (by positivity : 0<16*N^2*(N^r)^2)).mpr
  nlinarith [sq_nonneg Q]

end NLS.SequenceSpaces
