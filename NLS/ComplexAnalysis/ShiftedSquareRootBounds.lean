import NLS.ComplexAnalysis.EntireEvenSquareDescent
import Mathlib.Analysis.Real.Pi.Bounds

/-! # A fixed energy shift is small in the high frequency coordinate

The principal root of z²+c differs from z by at most |c|/Re(z) in the
right half-plane. Thus one cutoff makes this difference arbitrarily
small on every subsequent full free-centered frequency disc.
-/
noncomputable section
set_option autoImplicit false
open Complex Set Metric
namespace NLS.ComplexAnalysis

theorem re_sqrt_nonneg (w : ℂ) : 0 ≤ (sqrt w).re := by
  rw [Complex.sqrt,Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

theorem norm_sqrt_sq_add_sub_le (z c : ℂ) (hz : 0 < z.re) :
    ‖sqrt (z^2+c)-z‖ ≤ ‖c‖/z.re := by
  let w := sqrt (z^2+c)
  have he : (w-z)*(w+z) = c := by
    have hsq : w^2 = z^2+c := complex_sqrt_sq _
    calc
      _ = w^2-z^2 := by ring
      _ = c := by rw [hsq]; ring
  have hn : ‖w-z‖*‖w+z‖ = ‖c‖ := by rw [← norm_mul,he]
  have hre : z.re ≤ ‖w+z‖ := by
    have hw : 0 ≤ w.re := re_sqrt_nonneg _
    have h := re_le_norm (w+z)
    rw [add_re] at h
    linarith
  apply (le_div_iff₀ hz).mpr
  exact (mul_le_mul_of_nonneg_left hre (norm_nonneg (w-z))).trans_eq hn

theorem exists_high_disc_sqrt_shift_small (c : ℂ) (r delta : ℝ) (hd : 0 < delta) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
      0 < z.re ∧ ‖sqrt (z^2+c)-z‖ < delta := by
  obtain ⟨M,hM⟩ := exists_nat_gt ((r+‖c‖/delta+1)/Real.pi)
  let N := M+1
  have hN : r+‖c‖/delta+1 < Real.pi*(N : ℝ) := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hM
    dsimp [N]
    push_cast
    nlinarith [Real.pi_pos]
  refine ⟨N,by dsimp [N]; omega,?_⟩
  intro n hn z hz
  have hmn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hdist : ‖z-(Real.pi : ℂ)*n‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hre := (abs_le.mp ((abs_re_le_norm (z-(Real.pi : ℂ)*n)).trans hdist)).1
  have hreal : (z-(Real.pi : ℂ)*n).re = z.re-Real.pi*n := by simp
  rw [hreal] at hre
  have hzlarge : r+‖c‖/delta+1 < Real.pi*n := hN.trans_le (mul_le_mul_of_nonneg_left hmn Real.pi_pos.le)
  have hzpos : 0 < z.re := by
    have hc : 0 ≤ ‖c‖/delta := div_nonneg (norm_nonneg c) hd.le
    linarith
  refine ⟨hzpos,?_⟩
  have hb := (le_div_iff₀ hzpos).mp (norm_sqrt_sq_add_sub_le z c hzpos)
  have hratio : ‖c‖ < delta*z.re := by
    have hp : ‖c‖/delta < z.re := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ hd).mp hp
  exact (mul_lt_mul_iff_left₀ hzpos).mp (hb.trans_lt hratio)

end NLS.ComplexAnalysis
