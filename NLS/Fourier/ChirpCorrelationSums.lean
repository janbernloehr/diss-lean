import NLS.Fourier.AntitonePhaseCancellation
import NLS.Fourier.ChirpPhaseIncrements

/-! # Actual correlation sums for the phase printed in A.5 -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Fourier

/-- Unit-amplitude phase of the printed Fourier term, with arbitrary real linear part. -/
def chirpUnit (α x : ℝ) : ℂ := Complex.exp ((chirpPhase x+α*x : ℝ)*Complex.I)

/-- The correlation retains only a constant contribution from the linear part. -/
theorem chirpUnit_correlation (α x h : ℝ) :
    chirpUnit α (x+h)*star (chirpUnit α x) =
      Complex.exp ((chirpPhase (x+h)-chirpPhase x+α*h : ℝ)*Complex.I) := by
  simp only [chirpUnit,star_def,← Complex.exp_conj,map_mul,Complex.conj_ofReal,
    Complex.conj_I,← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Every correlation prefix in a dyadic block is bounded uniformly in the linear phase. -/
theorem norm_sum_chirp_correlations (N L h : ℕ) (α : ℝ)
    (hN : 1 ≤ N) (hh : 0 < h) (hL : L+h ≤ N) :
    ‖∑ n ∈ Finset.range L,
      chirpUnit α ((N : ℝ)+n+h)*star (chirpUnit α ((N : ℝ)+n))‖ ≤
        6*Real.pi*N/h := by
  let z : ℕ → ℂ := fun n =>
    Complex.exp ((chirpPhase ((N : ℝ)+n+h)-chirpPhase ((N : ℝ)+n)+α*h : ℝ)*Complex.I)
  let t : ℕ → ℝ := fun n =>
    (chirpPhaseIncrement ((N : ℝ)+n+h)-chirpPhaseIncrement ((N : ℝ)+n))/2
  let δ : ℝ := (h : ℝ)/(6*N)
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hhp : 0 < (h : ℝ) := by exact_mod_cast hh
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hm : Antitone t := by
    intro a b hab
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
    exact antitoneOn_chirpPhaseIncrement_shift h hhp.le
      (show 0 < (N : ℝ)+a by positivity) (show 0 < (N : ℝ)+b by positivity)
      (by exact_mod_cast Nat.add_le_add_left hab N)
  have ht (n : ℕ) (hn : n ≤ L) : δ ≤ t n ∧ t n ≤ Real.pi-δ := by
    have hb := chirpPhaseIncrement_half_shift_bounds N ((N : ℝ)+n) h
      (by exact_mod_cast hN) (le_add_of_nonneg_right (Nat.cast_nonneg n))
      (by exact_mod_cast (show N+n+h ≤ 2*N by omega)) hhp
      (by exact_mod_cast (show h ≤ N by omega))
    have hδu : δ ≤ 1/6 := by
      dsimp only [δ]
      apply (div_le_iff₀ (by positivity : 0 < 6*(N : ℝ))).mpr
      have : (h : ℝ) ≤ N := by exact_mod_cast (show h ≤ N by omega)
      linarith
    exact ⟨hb.1,by dsimp only [t]; linarith [hb.2,Real.two_le_pi]⟩
  have hz (n : ℕ) (_ : n ≤ L) : ‖z n‖ ≤ 1 := by
    simp only [z,Complex.norm_exp_ofReal_mul_I,le_refl]
  have hs (n : ℕ) (_ : n < L) : z (n+1) = Complex.exp ((2*t n : ℝ)*Complex.I)*z n := by
    dsimp only [z,t]
    rw [← Complex.exp_add]
    congr 1
    have he (x : ℝ) : chirpPhase (x+1+h)-chirpPhase (x+1)+α*h =
        (chirpPhaseIncrement (x+h)-chirpPhaseIncrement x)+
          (chirpPhase (x+h)-chirpPhase x+α*h) := by
      dsimp only [chirpPhaseIncrement]
      rw [show x+1+h = x+h+1 by ring]
      ring
    simp only [Nat.cast_add,Nat.cast_one]
    rw [show (N : ℝ)+(n+1) = ((N : ℝ)+n)+1 by ring,he]
    push_cast
    ring
  have hb := norm_sum_range_le_of_separated_antitone_half_increments z t L δ hδ ht hm hz hs
  have he : Real.pi/δ = 6*Real.pi*N/h := by dsimp only [δ]; field_simp
  rw [he] at hb
  simpa only [chirpUnit_correlation,z] using hb

end NLS.Fourier
