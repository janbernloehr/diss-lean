import NLS.Fourier.OscillatorySumVariation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Reciprocal multipliers away from a phase resonance -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Fourier

/-- Reciprocal of exp(2it)-1, in coordinates suited to variation estimates. -/
def phaseReciprocalMultiplier (t : ℝ) : ℂ :=
  ⟨-1/2,-Real.cos t/(2*Real.sin t)⟩

theorem phaseReciprocalMultiplier_mul (t : ℝ) (ht : Real.sin t ≠ 0) :
    phaseReciprocalMultiplier t*(Complex.exp ((2*t : ℝ)*Complex.I)-1) = 1 := by
  apply Complex.ext
  · simp only [phaseReciprocalMultiplier,Complex.mul_re,Complex.sub_re,
      Complex.exp_ofReal_mul_I_re,Complex.one_re,Complex.sub_im,
      Complex.exp_ofReal_mul_I_im,Complex.one_im,sub_zero]
    rw [Real.cos_two_mul_eq_one_sub,Real.sin_two_mul]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq t]
  · simp only [phaseReciprocalMultiplier,Complex.mul_im,Complex.sub_re,
      Complex.exp_ofReal_mul_I_re,Complex.one_re,Complex.sub_im,
      Complex.exp_ofReal_mul_I_im,Complex.one_im,sub_zero]
    rw [Real.cos_two_mul_eq_one_sub,Real.sin_two_mul]
    field_simp
    ring

/-- The imaginary part is monotone on the entire resonance-free interval. -/
theorem monotoneOn_im_phaseReciprocalMultiplier :
    MonotoneOn (fun t => (phaseReciprocalMultiplier t).im) (Ioo 0 Real.pi) := by
  intro x hx y hy hxy
  have hsx := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsy := Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2
  change -Real.cos x/(2*Real.sin x) ≤ -Real.cos y/(2*Real.sin y)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hs := Real.sin_nonneg_of_mem_Icc (show y-x ∈ Icc 0 Real.pi from
    ⟨by linarith,by linarith [hx.1,hy.2]⟩)
  rw [Real.sin_sub] at hs
  nlinarith

/-- The real part is constant, so the norm of an increment is its imaginary increment. -/
theorem norm_phaseReciprocalMultiplier_sub (x y : ℝ)
    (hx : x ∈ Ioo 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi) (hxy : x ≤ y) :
    ‖phaseReciprocalMultiplier y-phaseReciprocalMultiplier x‖ =
      (phaseReciprocalMultiplier y).im-(phaseReciprocalMultiplier x).im := by
  have he : phaseReciprocalMultiplier y-phaseReciprocalMultiplier x =
      (((phaseReciprocalMultiplier y).im-(phaseReciprocalMultiplier x).im : ℝ) : ℂ)*Complex.I := by
    apply Complex.ext <;>
      simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        phaseReciprocalMultiplier] <;> ring
  rw [he,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (monotoneOn_im_phaseReciprocalMultiplier hx hy hxy))]

/-- The exact multiplier norm on the positive-sine interval. -/
theorem norm_phaseReciprocalMultiplier (t : ℝ) (ht : t ∈ Ioo 0 Real.pi) :
    ‖phaseReciprocalMultiplier t‖ = 1/(2*Real.sin t) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have he : ‖Complex.exp ((2*t : ℝ)*Complex.I)-1‖ = 2*Real.sin t := by
    rw [mul_comm,Complex.norm_exp_I_mul_ofReal_sub_one]
    simp [Real.norm_eq_abs,abs_of_pos hs]
  have h := congrArg norm (phaseReciprocalMultiplier_mul t hs.ne')
  rw [norm_mul,norm_one,he] at h
  exact (eq_div_iff (by positivity)).mpr h

/-- Separation from the two neighboring phase resonances bounds the multiplier. -/
theorem norm_phaseReciprocalMultiplier_le (δ t : ℝ) (hδ : 0 < δ)
    (hl : δ ≤ t) (hr : t ≤ Real.pi-δ) :
    ‖phaseReciprocalMultiplier t‖ ≤ Real.pi/(4*δ) := by
  have ht : t ∈ Ioo 0 Real.pi := ⟨by linarith,by linarith⟩
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hb : 2*δ/Real.pi ≤ Real.sin t := by
    by_cases hm : t ≤ Real.pi/2
    · have h := Real.mul_le_sin ht.1.le hm
      have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2/Real.pi by positivity)
      simpa only [div_mul_eq_mul_div] using hh.trans h
    · have h := Real.mul_le_sin (show 0 ≤ Real.pi-t by linarith)
        (show Real.pi-t ≤ Real.pi/2 by linarith)
      rw [Real.sin_pi_sub] at h
      have hh := mul_le_mul_of_nonneg_left (show δ ≤ Real.pi-t by linarith)
        (show 0 ≤ 2/Real.pi by positivity)
      simpa only [div_mul_eq_mul_div] using hh.trans h
  rw [norm_phaseReciprocalMultiplier t ht]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h := (div_le_iff₀ Real.pi_pos).mp hb
  nlinarith

/-- Along an increasing phase, total multiplier variation telescopes exactly. -/
theorem sum_norm_phaseReciprocalMultiplier_differences (t : ℕ → ℝ) (N : ℕ)
    (ht : ∀ n ≤ N, t n ∈ Ioo 0 Real.pi) (hm : Monotone t) :
    (∑ n ∈ Finset.range N,
      ‖phaseReciprocalMultiplier (t (n+1))-phaseReciprocalMultiplier (t n)‖) =
      (phaseReciprocalMultiplier (t N)).im-(phaseReciprocalMultiplier (t 0)).im := by
  have he : (∑ n ∈ Finset.range N,
      ‖phaseReciprocalMultiplier (t (n+1))-phaseReciprocalMultiplier (t n)‖) =
      ∑ n ∈ Finset.range N,
        ((phaseReciprocalMultiplier (t (n+1))).im-(phaseReciprocalMultiplier (t n)).im) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnN := Finset.mem_range.mp hn
    exact norm_phaseReciprocalMultiplier_sub _ _ (ht n (by omega))
      (ht (n+1) (by omega)) (hm (by omega))
  rw [he]
  have htel (k : ℕ) : (∑ n ∈ Finset.range k,
        ((phaseReciprocalMultiplier (t (n+1))).im-(phaseReciprocalMultiplier (t n)).im)) =
      (phaseReciprocalMultiplier (t k)).im-(phaseReciprocalMultiplier (t 0)).im := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ,ih]; ring
  exact htel N

/-- Uniform cancellation for monotone half-increments separated from resonance. -/
theorem norm_sum_range_le_of_separated_half_increments
    (z : ℕ → ℂ) (t : ℕ → ℝ) (N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (ht : ∀ n ≤ N, δ ≤ t n ∧ t n ≤ Real.pi-δ) (hm : Monotone t)
    (hz : ∀ n ≤ N, ‖z n‖ ≤ 1)
    (hstep : ∀ n < N, z (n+1) = Complex.exp ((2*t n : ℝ)*Complex.I)*z n) :
    ‖∑ n ∈ Finset.range N, z n‖ ≤ Real.pi/δ := by
  let b : ℕ → ℂ := fun n => phaseReciprocalMultiplier (t n)
  let B : ℝ := Real.pi/(4*δ)
  have hb (n : ℕ) (hn : n ≤ N) : ‖b n‖ ≤ B :=
    norm_phaseReciprocalMultiplier_le δ (t n) hδ (ht n hn).1 (ht n hn).2
  have hi (n : ℕ) (hn : n ≤ N) : t n ∈ Ioo 0 Real.pi := by
    have h := ht n hn
    exact ⟨by linarith,by linarith⟩
  have hv : (∑ n ∈ Finset.range N, ‖b (n+1)-b n‖) ≤ 2*B := by
    rw [show (∑ n ∈ Finset.range N, ‖b (n+1)-b n‖) =
      (b N).im-(b 0).im from sum_norm_phaseReciprocalMultiplier_differences t N hi hm]
    have hN := (le_abs_self (b N).im).trans (Complex.abs_im_le_norm (b N))
    have h0 := (neg_le_abs (b 0).im).trans (Complex.abs_im_le_norm (b 0))
    linarith [hb N le_rfl,hb 0 (Nat.zero_le _)]
  have hr (n : ℕ) (hn : n < N) : b n*(z (n+1)-z n) = z n := by
    rw [hstep n hn]
    have hid := phaseReciprocalMultiplier_mul (t n)
      (Real.sin_pos_of_pos_of_lt_pi (hi n hn.le).1 (hi n hn.le).2).ne'
    calc
      _ = (b n*(Complex.exp ((2*t n : ℝ)*Complex.I)-1))*z n := by ring
      _ = z n := by rw [hid,one_mul]
  have h := norm_sum_range_le_of_multiplier_variation z b N B (2*B) hz
    (hb 0 (Nat.zero_le _)) (hb N le_rfl) hr hv
  have he : 2*B+2*B = Real.pi/δ := by dsimp only [B]; ring
  exact h.trans_eq he

end NLS.Fourier
