import NLS.Fourier.ChirpCorrelationSums
import NLS.Fourier.FiniteCorrelationIdentity
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Uniform block cancellation for the printed chirp -/
noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.Fourier

/-- A finite harmonic estimate for every prefix of an original dyadic chirp block. -/
theorem norm_sum_chirpUnit_sq_le_harmonic (N M : ℕ) (α : ℝ)
    (hN : 1 ≤ N) (hM : M ≤ N) :
    ‖∑ n ∈ Finset.range M, chirpUnit α ((N : ℝ)+n)‖^2 ≤
      M+12*Real.pi*N*(harmonic M : ℝ) := by
  have hb := norm_sum_range_sq_le_correlations (fun n => chirpUnit α ((N : ℝ)+n)) M
  have hd : (∑ n ∈ Finset.range M, ‖chirpUnit α ((N : ℝ)+n)‖^2) = M := by
    simp only [chirpUnit,Complex.norm_exp_ofReal_mul_I,one_pow,Finset.sum_const,
      Finset.card_range,nsmul_eq_mul,mul_one]
  rw [hd] at hb
  have hc (r : ℕ) (hr : r ∈ Finset.range M) :
      ‖∑ n ∈ Finset.range (M-(r+1)),
        chirpUnit α ((N : ℝ)+(n+r+1))*star (chirpUnit α ((N : ℝ)+n))‖ ≤
          6*Real.pi*N/(r+1) := by
    have hrM := Finset.mem_range.mp hr
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using
      norm_sum_chirp_correlations N (M-(r+1)) (r+1) α hN (by omega) (by omega)
  have hc' := Finset.sum_le_sum hc
  have he : (∑ r ∈ Finset.range M, 6*Real.pi*N/((r : ℝ)+1)) =
      6*Real.pi*N*(harmonic M : ℝ) := by
    simp [harmonic,Finset.mul_sum,div_eq_mul_inv]
  rw [he] at hc'
  simp only [Nat.cast_add,Nat.cast_one] at hb
  nlinarith

/-- Uniform cancellation for all block prefixes and all real linear phases. -/
theorem norm_sum_chirpUnit_sq_le_log (N M : ℕ) (α : ℝ)
    (hN : 1 ≤ N) (hM : M ≤ N) :
    ‖∑ n ∈ Finset.range M, chirpUnit α ((N : ℝ)+n)‖^2 ≤
      N+12*Real.pi*N*(1+Real.log N) := by
  have hm : (harmonic M : ℝ) ≤ harmonic N := by
    simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hM)
      (fun i _ _ => by positivity)
  have hb := norm_sum_chirpUnit_sq_le_harmonic N M α hN hM
  have hc := mul_le_mul_of_nonneg_left (hm.trans (harmonic_le_one_add_log N))
    (show 0 ≤ 12*Real.pi*(N : ℝ) by positivity)
  have hMc : (M : ℝ) ≤ N := by exact_mod_cast hM
  linarith

/-- A direct square-root form of the uniform cancellation estimate. -/
theorem norm_sum_chirpUnit_le_sqrt (N M : ℕ) (α : ℝ)
    (hN : 1 ≤ N) (hM : M ≤ N) :
    ‖∑ n ∈ Finset.range M, chirpUnit α ((N : ℝ)+n)‖ ≤
      Real.sqrt (N+12*Real.pi*N*(1+Real.log N)) := by
  exact Real.le_sqrt_of_sq_le (norm_sum_chirpUnit_sq_le_log N M α hN hM)

/-- The exact oscillatory factors printed in A.5 satisfy the same bound at every physical point. -/
theorem norm_sum_printedChirp_phases_le (N M : ℕ) (x : ℝ)
    (hN : 1 ≤ N) (hM : M ≤ N) :
    ‖∑ n ∈ Finset.range M,
      Complex.exp (Complex.I*(((N : ℝ)+n)*Real.log ((N : ℝ)+n))) *
        Complex.exp (Complex.I*(((N : ℝ)+n)*Real.pi*x))‖ ≤
      Real.sqrt (N+12*Real.pi*N*(1+Real.log N)) := by
  have he (n : ℕ) : chirpUnit (Real.pi*x) ((N : ℝ)+n) =
      Complex.exp (Complex.I*(((N : ℝ)+n)*Real.log ((N : ℝ)+n))) *
        Complex.exp (Complex.I*(((N : ℝ)+n)*Real.pi*x)) := by
    rw [chirpUnit,chirpPhase,← Complex.exp_add]
    congr 1
    push_cast
    ring
  simpa only [he] using norm_sum_chirpUnit_le_sqrt N M (Real.pi*x) hN hM

end NLS.Fourier
