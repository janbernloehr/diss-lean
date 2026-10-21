import NLS.Fourier.ChirpBlockCancellation
import NLS.Fourier.MonotoneWeightedSums
import NLS.Fourier.PrintedChirpAmplitude

/-! # Weighted block estimates for the literal printed A.5 series -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.Fourier

/-- Every weighted prefix inherits the uniform unweighted cancellation bound. -/
theorem norm_sum_weighted_chirpUnit_le (N M : ℕ) (α : ℝ)
    (hN : 2 ≤ N) (hM : M ≤ N) :
    ‖∑ n ∈ Finset.range M,
      (printedChirpAmplitude ((N : ℝ)+n) : ℂ)*chirpUnit α ((N : ℝ)+n)‖ ≤
      printedChirpAmplitude N * Real.sqrt (N+12*Real.pi*N*(1+Real.log N)) := by
  have hm : Antitone (fun n : ℕ => printedChirpAmplitude ((N : ℝ)+n)) := by
    intro a b hab
    apply antitoneOn_printedChirpAmplitude
    · change 2 ≤ (N : ℝ)+a
      exact_mod_cast (show 2 ≤ N+a by omega)
    · change 2 ≤ (N : ℝ)+b
      exact_mod_cast (show 2 ≤ N+b by omega)
    · exact_mod_cast Nat.add_le_add_left hab N
  simpa only [Nat.cast_zero,add_zero] using
    norm_sum_range_weighted_le (fun n => chirpUnit α ((N : ℝ)+n))
      (fun n => printedChirpAmplitude ((N : ℝ)+n)) M
      (Real.sqrt (N+12*Real.pi*N*(1+Real.log N)))
      (fun n _ => printedChirpAmplitude_nonneg _) hm
      (fun m hm => norm_sum_chirpUnit_le_sqrt N m α (by omega) (hm.trans hM))

/-- The square-root growth cancels the square-root in the printed denominator. -/
theorem printedChirpAmplitude_mul_sqrt_bound (x : ℝ) (hx : 0 < x) :
    printedChirpAmplitude x * Real.sqrt (x+12*Real.pi*x*(1+Real.log x)) =
      Real.sqrt (1+12*Real.pi*(1+Real.log x))/(Real.log x)^2 := by
  rw [show x+12*Real.pi*x*(1+Real.log x) = x*(1+12*Real.pi*(1+Real.log x)) by ring,
    Real.sqrt_mul hx.le,printedChirpAmplitude]
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  field_simp

/-- A fixed constant for summable dyadic block estimates. -/
def chirpDyadicBoundConstant : ℝ :=
  Real.sqrt (1+12*Real.pi*(1+Real.log 2))/(Real.log 2)^2

theorem chirpDyadicBoundConstant_nonneg : 0 ≤ chirpDyadicBoundConstant := by
  unfold chirpDyadicBoundConstant
  positivity

/-- The exact printed weight gives a summable power of the dyadic block index. -/
theorem printedChirpAmplitude_dyadic_bound (k : ℕ) (hk : 1 ≤ k) :
    printedChirpAmplitude ((2 : ℝ)^k) *
      Real.sqrt ((2 : ℝ)^k+12*Real.pi*(2 : ℝ)^k*(1+Real.log ((2 : ℝ)^k))) ≤
      chirpDyadicBoundConstant/(k : ℝ)^(3/2 : ℝ) := by
  have hkp : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [printedChirpAmplitude_mul_sqrt_bound _ (by positivity),Real.log_pow]
  have hD : 1+12*Real.pi*(1+(k : ℝ)*Real.log 2) ≤
      (k : ℝ)*(1+12*Real.pi*(1+Real.log 2)) := by
    have h := mul_le_mul_of_nonneg_right hk1 (show 0 ≤ 1+12*Real.pi by positivity)
    nlinarith
  have hs := Real.sqrt_le_sqrt hD
  rw [Real.sqrt_mul hkp.le] at hs
  have hr : Real.sqrt (k : ℝ)/(k : ℝ)^2 = 1/(k : ℝ)^(3/2 : ℝ) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_two,← Real.rpow_sub hkp]
    norm_num
    rw [Real.rpow_neg hkp.le]
  calc
    _ ≤ (Real.sqrt (k : ℝ)*Real.sqrt (1+12*Real.pi*(1+Real.log 2))) /
        ((k : ℝ)*Real.log 2)^2 :=
      div_le_div_of_nonneg_right hs (sq_nonneg _)
    _ = chirpDyadicBoundConstant*(Real.sqrt (k : ℝ)/(k : ℝ)^2) := by
      unfold chirpDyadicBoundConstant
      field_simp
    _ = _ := by rw [hr]; ring

/-- Every weighted dyadic prefix has a bound summable over the dyadic index. -/
theorem norm_sum_weighted_chirpUnit_dyadic_le (k M : ℕ) (α : ℝ)
    (hk : 1 ≤ k) (hM : M ≤ 2^k) :
    ‖∑ n ∈ Finset.range M,
      (printedChirpAmplitude ((2 : ℝ)^k+n) : ℂ)*chirpUnit α ((2 : ℝ)^k+n)‖ ≤
      chirpDyadicBoundConstant/(k : ℝ)^(3/2 : ℝ) := by
  have htwo : 2 ≤ 2^k := by
    calc 2 = 2^1 := by norm_num
         _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hb := norm_sum_weighted_chirpUnit_le (2^k) M α htwo hM
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hb
  exact hb.trans (printedChirpAmplitude_dyadic_bound k hk)

theorem summable_chirp_dyadic_majorant :
    Summable (fun k : ℕ => chirpDyadicBoundConstant/(k : ℝ)^(3/2 : ℝ)) := by
  simpa only [div_eq_mul_inv,one_mul] using
    (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ)<3/2)).mul_left
      chirpDyadicBoundConstant

end NLS.Fourier
