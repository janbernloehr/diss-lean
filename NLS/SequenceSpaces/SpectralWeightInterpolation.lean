import NLS.SequenceSpaces.SpectralWeight

/-! # The piecewise-linear extension of source weights

Section 23 evaluates weights at real arguments by linear interpolation of
integer values. Symmetry extends the interpolation to negative arguments.
-/
noncomputable section
namespace NLS.SpectralWeight

/-- The source notation `w[t]`: affine between consecutive nonnegative integers,
extended evenly to the real line. -/
def realExtension (w : SpectralWeight) (t : ℝ) : ℝ :=
  let n := ⌊|t|⌋₊
  w n + (|t| - n) * (w (n+1) - w n)

@[simp] theorem realExtension_neg (w : SpectralWeight) (t : ℝ) :
    w.realExtension (-t) = w.realExtension t := by simp [realExtension]

@[simp] theorem realExtension_natCast (w : SpectralWeight) (n : ℕ) :
    w.realExtension n = w n := by simp [realExtension]

@[simp] theorem realExtension_intCast (w : SpectralWeight) (n : ℤ) :
    w.realExtension n = w n := by
  have h : |(n : ℝ)| = (n.natAbs : ℝ) := by simp
  simp only [realExtension,h,Nat.floor_natCast,sub_self,zero_mul,add_zero,
    Int.natCast_natAbs,apply_abs]

/-- Interpolation stays between the two adjacent integer values. -/
theorem realExtension_bounds (w : SpectralWeight) (t : ℝ) :
    w (⌊|t|⌋₊ : ℤ) ≤ w.realExtension t ∧
      w.realExtension t ≤ w ((⌊|t|⌋₊ : ℤ)+1) := by
  have hd : 0 ≤ w ((⌊|t|⌋₊ : ℤ)+1) - w (⌊|t|⌋₊ : ℤ) := by
    exact sub_nonneg.mpr (by exact_mod_cast w.monotone_nat (Nat.le_succ ⌊|t|⌋₊))
  have hl := Nat.floor_le (abs_nonneg t)
  have hu := Nat.lt_floor_add_one |t|
  dsimp [realExtension]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hl) hd,
    mul_nonneg (by linarith : 0 ≤ 1-(|t|-(⌊|t|⌋₊ : ℝ))) hd]

/-- The extension preserves the source lower normalization, including scaled weights. -/
theorem one_le_realExtension (w : SpectralWeight) (t : ℝ) : 1 ≤ w.realExtension t :=
  (w.one_le _).trans (w.realExtension_bounds t).1

theorem realExtension_pos (w : SpectralWeight) (t : ℝ) : 0 < w.realExtension t :=
  zero_lt_one.trans_le (w.one_le_realExtension t)

/-- Increasing the magnitude of a real argument can only increase the weight. -/
theorem realExtension_mono_abs (w : SpectralWeight) {s t : ℝ} (h : |s| ≤ |t|) :
    w.realExtension s ≤ w.realExtension t := by
  have hf := Nat.floor_mono h
  rcases eq_or_lt_of_le hf with he | hl
  · have hd : 0 ≤ w ((⌊|t|⌋₊ : ℤ)+1)-w (⌊|t|⌋₊ : ℤ) := by
      exact sub_nonneg.mpr (by exact_mod_cast w.monotone_nat (Nat.le_succ ⌊|t|⌋₊))
    dsimp [realExtension]
    rw [he]
    exact add_le_add_right (mul_le_mul_of_nonneg_right (sub_le_sub_right h _) hd) _
  · have hm : w ((⌊|s|⌋₊ : ℤ)+1) ≤ w (⌊|t|⌋₊ : ℤ) := by
      exact_mod_cast w.monotone_nat (Nat.succ_le_of_lt hl)
    exact (w.realExtension_bounds s).2.trans (hm.trans (w.realExtension_bounds t).1)

/-- A signed Fourier index inside a real cutoff is bounded by the interpolated weight. -/
theorem le_realExtension (w : SpectralWeight) (n : ℤ) (t : ℝ) (h : |(n : ℝ)| ≤ t) :
    w n ≤ w.realExtension t := by
  rw [← w.realExtension_intCast n]
  exact w.realExtension_mono_abs (h.trans (le_abs_self t))

/-- Exact affine formula, including both endpoints of each unit interval. -/
theorem realExtension_affine (w : SpectralWeight) (n : ℕ) (u : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    w.realExtension ((n : ℝ)+u) = (1-u)*w n+u*w ((n : ℤ)+1) := by
  by_cases he : u = 1
  · subst u
    have hn : (n : ℝ)+1 = ((n+1 : ℕ) : ℝ) := by push_cast; rfl
    rw [hn,realExtension_natCast]
    simp
  · have hu' : u < 1 := lt_of_le_of_ne hu1 he
    have hf : ⌊(n : ℝ)+u⌋₊ = n := by
      apply Nat.floor_eq_iff (by positivity) |>.mpr
      constructor <;> linarith
    simp only [realExtension,abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)+u),hf]
    ring

end NLS.SpectralWeight
