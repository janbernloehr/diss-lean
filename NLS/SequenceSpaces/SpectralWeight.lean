import NLS.SequenceSpaces.TemperedWeight

/-!
# The weight class in Section 6

The source's class `M` consists of weights bounded below by one, symmetric,
submultiplicative, and increasing along nonnegative integer indices. The
normalization is the displayed lower bound; it does not require `w(0)=1`.
Scaled Sobolev weights include the exact source convention `(1+|nπ|)^s`.
-/

noncomputable section
namespace NLS

/-- The normalized, symmetric, monotone submultiplicative weights of Section 6. -/
structure SpectralWeight extends Weight where
  one_le : ∀ n, 1 ≤ value n
  neg_eq : ∀ n, value (-n) = value n
  add_le : ∀ m n, value (m + n) ≤ value m * value n
  monotone_nat : Monotone (fun n : ℕ => value (n : ℤ))

instance : CoeFun SpectralWeight (fun _ => ℤ → ℝ) := ⟨fun w => w.toWeight.value⟩

namespace SpectralWeight

@[simp] theorem toWeight_apply (w : SpectralWeight) (n : ℤ) : w.toWeight n = w n := rfl

@[simp] theorem apply_neg (w : SpectralWeight) (n : ℤ) : w (-n) = w n := w.neg_eq n

@[simp] theorem apply_abs (w : SpectralWeight) (n : ℤ) : w |n| = w n := by
  by_cases hn : 0 ≤ n
  · rw [abs_of_nonneg hn]
  · rw [abs_of_neg (lt_of_not_ge hn), apply_neg]

/-- The source's monotonicity condition controls all signed frequency magnitudes. -/
theorem mono_abs (w : SpectralWeight) {m n : ℤ} (h : |m| ≤ |n|) : w m ≤ w n := by
  have hn : m.natAbs ≤ n.natAbs := by
    rw [← Nat.cast_le (α := ℤ)]
    simpa only [Int.natCast_natAbs] using h
  simpa only [Int.natCast_natAbs, apply_abs] using w.monotone_nat hn

/-- Every source weight is compatible with the existing tempered-distribution realization. -/
theorem hasTemperedInverse (w : SpectralWeight) : w.toWeight.HasTemperedInverse := by
  refine ⟨0, 1, by norm_num, fun n => ?_⟩
  simpa only [pow_zero, mul_one, div_one] using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (w.one_le n))

/-- The source allows constant weights greater than one. -/
def constant (c : ℝ) (hc : 1 ≤ c) : SpectralWeight where
  value _ := c
  positive _ := lt_of_lt_of_le zero_lt_one hc
  one_le _ := hc
  neg_eq _ := rfl
  add_le _ _ := by nlinarith
  monotone_nat _ _ _ := le_rfl

/-- Unit weight gives the unweighted scale. -/
def one : SpectralWeight := constant 1 le_rfl

@[simp] theorem constant_apply (c : ℝ) (hc : 1 ≤ c) (n : ℤ) : constant c hc n = c := rfl
@[simp] theorem one_apply (n : ℤ) : one n = 1 := rfl

/-- Scaled inhomogeneous Sobolev weights, with every nonnegative scale and regularity. -/
def scaledSobolev (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s) : SpectralWeight where
  value n := (1 + c * |(n : ℝ)|) ^ s
  positive n := Real.rpow_pos_of_pos (by positivity) s
  one_le n := Real.one_le_rpow (by linarith [mul_nonneg hc (abs_nonneg (n : ℝ))]) hs
  neg_eq n := by simp
  add_le m n := by
    have htriangle : |((m + n : ℤ) : ℝ)| ≤ |(m : ℝ)| + |(n : ℝ)| := by
      simpa only [Int.cast_add] using abs_add_le (m : ℝ) (n : ℝ)
    have hb : 1 + c * |((m + n : ℤ) : ℝ)| ≤ (1 + c * |(m : ℝ)|) * (1 + c * |(n : ℝ)|) := by
      have ht := mul_le_mul_of_nonneg_left htriangle hc
      have hp : 0 ≤ (c * |(m : ℝ)|) * (c * |(n : ℝ)|) := by positivity
      nlinarith
    exact (Real.rpow_le_rpow (by positivity) hb hs).trans_eq
      (Real.mul_rpow (by positivity) (by positivity))
  monotone_nat m n hmn := by
    apply Real.rpow_le_rpow (by positivity) _ hs
    simp only [Int.cast_natCast, Nat.abs_cast]
    gcongr

@[simp] theorem scaledSobolev_apply (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s) (n : ℤ) :
    scaledSobolev c s hc hs n = (1 + c * |(n : ℝ)|) ^ s := rfl

/-- The normalized-frequency Sobolev weight already used in the library belongs to the source class. -/
def sobolev (s : ℝ) (hs : 0 ≤ s) : SpectralWeight := scaledSobolev 1 s zero_le_one hs

@[simp] theorem sobolev_apply (s : ℝ) (hs : 0 ≤ s) (n : ℤ) : sobolev s hs n = Weight.sobolev s n := by
  simp [sobolev]

/-- The exact `⟨nπ⟩^s` weight in Section 6. -/
def piSobolev (s : ℝ) (hs : 0 ≤ s) : SpectralWeight := scaledSobolev Real.pi s Real.pi_pos.le hs

@[simp] theorem piSobolev_apply (s : ℝ) (hs : 0 ≤ s) (n : ℤ) :
    piSobolev s hs n = (1 + |(n : ℝ) * Real.pi|) ^ s := by
  simp only [piSobolev, scaledSobolev_apply, abs_mul, abs_of_pos Real.pi_pos, mul_comm Real.pi]

/-- Symmetry turns submultiplicativity into a reverse comparison under any lattice shift. -/
theorem le_shift_mul (w : SpectralWeight) (n i : ℤ) : w n ≤ w (n + i) * w i := by
  simpa only [add_neg_cancel_right, apply_neg] using w.add_le (n + i) (-i)

/-- Ratios of translated weights are controlled solely by the translation. -/
theorem shift_ratio_le (w : SpectralWeight) (n i : ℤ) : w (n + i) / w n ≤ w i := by
  apply (div_le_iff₀ (w.positive n)).mpr
  simpa only [mul_comm] using w.add_le n i

end SpectralWeight
end NLS
