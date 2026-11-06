import NLS.KdV.HillHighRegularCorrectionDecay
import NLS.SequenceSpaces.ReciprocalSquareTail

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
include h0q h0r

theorem summable_norm_hillRegularAbelianCorrection (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun k : ℕ => ‖hillRegularAbelianCorrection q hq hr n hn (k+1) (by omega)‖) := by
  obtain ⟨N,hN,C,hC,hbound⟩ := exists_hillRegularAbelianCorrection_quadratic_decay h0q h0r q hq hr n hn
  have hmajor : Summable (fun k : ℕ => C/((k : ℝ)+1)^2) := by
    simpa only [mul_one_div,Nat.cast_one] using (NLS.ReciprocalSeries.summable_nat_reciprocal_sq_tail 1 (by omega)).mul_left C
  apply hmajor.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun k hk => hk⟩] with k hk
  simpa only [norm_norm,Nat.cast_add,Nat.cast_one] using hbound (k+1) (by omega) (by omega)

theorem summable_hillRegularAbelianCorrection (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun k : ℕ => hillRegularAbelianCorrection q hq hr n hn (k+1) (by omega)) :=
  (summable_norm_hillRegularAbelianCorrection h0q h0r q hq hr n hn).of_norm

omit h0q h0r in
def hillSummedRegularAbelianCorrection (n : ℕ) (hn : 1 ≤ n) : ℂ :=
  ∑' k : ℕ, hillRegularAbelianCorrection q hq hr n hn (k+1) (by omega)

theorem hillSummedRegularAbelianCorrection_im_eq_zero (n : ℕ) (hn : 1 ≤ n) :
    (hillSummedRegularAbelianCorrection q hq hr n hn).im = 0 := by
  rw [hillSummedRegularAbelianCorrection, Complex.im_tsum (summable_hillRegularAbelianCorrection h0q h0r q hq hr n hn)]
  simp only [hillRegularAbelianCorrection_im_eq_zero,tsum_zero]

theorem norm_hillSummedRegularAbelianCorrection_le (n : ℕ) (hn : 1 ≤ n) :
    ‖hillSummedRegularAbelianCorrection q hq hr n hn‖ ≤
      ∑' k : ℕ, ‖hillRegularAbelianCorrection q hq hr n hn (k+1) (by omega)‖ :=
  norm_tsum_le_tsum_norm (summable_norm_hillRegularAbelianCorrection h0q h0r q hq hr n hn)

theorem exists_hillRegularAbelianCorrection_absolute_tail_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, N ≤ L → ∀ hL : 1 ≤ L,
      (∑' k : ℕ, ‖hillRegularAbelianCorrection q hq hr n hn (k+L) (by omega)‖) ≤ 2*C/(L : ℝ) := by
  obtain ⟨N,hN,C,hC,hbound⟩ := exists_hillRegularAbelianCorrection_quadratic_decay h0q h0r q hq hr n hn
  refine ⟨N,hN,C,hC,?_⟩
  intro L hNL hL
  have hmajor : Summable (fun k : ℕ => C/((k : ℝ)+L)^2) := by
    simpa only [mul_one_div] using (NLS.ReciprocalSeries.summable_nat_reciprocal_sq_tail L hL).mul_left C
  have hb (k : ℕ) : ‖hillRegularAbelianCorrection q hq hr n hn (k+L) (by omega)‖ ≤ C/((k : ℝ)+L)^2 := by
    simpa only [Nat.cast_add] using hbound (k+L) (by omega) (by omega)
  have hs : Summable (fun k : ℕ => ‖hillRegularAbelianCorrection q hq hr n hn (k+L) (by omega)‖) :=
    hmajor.of_norm_bounded (fun k => by simpa only [norm_norm] using hb k)
  calc
    _ ≤ ∑' k : ℕ, C/((k : ℝ)+L)^2 := hs.tsum_le_tsum hb hmajor
    _ = C*(∑' k : ℕ, 1/((k : ℝ)+L)^2) := by rw [← tsum_mul_left];simp only [mul_one_div]
    _ ≤ C*(2/(L : ℝ)) := mul_le_mul_of_nonneg_left (NLS.ReciprocalSeries.tsum_nat_reciprocal_sq_tail_le L hL) hC.le
    _ = _ := by ring

end NLS.KdV
