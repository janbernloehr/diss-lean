import NLS.Fourier.PerturbedHilbertRows

/-!
# Square-kernel bounds for separated reciprocal rows

A row sampled at a physical midpoint can be compared with the same row
sampled at the free lattice.  Linear separation of both denominators and
a bounded midpoint displacement make their difference a square-kernel
convolution, hence an `ℓp` row sequence.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier

/-- Changing a separated reciprocal denominator gains one extra reciprocal
index factor. -/
theorem norm_div_sub_div_le_of_separation
    (C R d : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 < d)
    (a x y : ℂ) (hx : d ≤ C*‖x‖) (hy : d ≤ ‖y‖)
    (hxy : ‖x-y‖ ≤ R) :
    ‖a/x-a/y‖ ≤ C*R*‖a‖*d⁻¹^2 := by
  have hCpos : 0 < C := by
    by_contra hn
    have : C = 0 := le_antisymm (le_of_not_gt hn) hC
    simp [this] at hx
    linarith
  have hxn : 0 < ‖x‖ := by nlinarith
  have hyn : 0 < ‖y‖ := by linarith
  have hx0 : x ≠ 0 := by simpa only [norm_pos_iff] using hxn
  have hy0 : y ≠ 0 := by simpa only [norm_pos_iff] using hyn
  have hident : a/x-a/y = a*(y-x)/(x*y) := by
    field_simp
  have hxi : ‖x‖⁻¹ ≤ C*d⁻¹ := by
    calc
      ‖x‖⁻¹ = 1/‖x‖ := by ring
      _ ≤ C/d := (div_le_div_iff₀ hxn hd).mpr (by simpa using hx)
      _ = C*d⁻¹ := by ring
  have hyi : ‖y‖⁻¹ ≤ d⁻¹ := by
    simpa only [one_div] using (one_div_le_one_div_of_le hd hy)
  calc
    ‖a/x-a/y‖ = ‖a‖*‖x-y‖*(‖x‖⁻¹*‖y‖⁻¹) := by
      rw [hident]
      simp only [norm_div, norm_mul, norm_sub_rev]
      ring
    _ ≤ ‖a‖*R*((C*d⁻¹)*d⁻¹) := by
          gcongr
    _ = C*R*‖a‖*d⁻¹^2 := by ring

/-- The correction between arbitrary physical and free sampled rows. -/
def separatedReciprocalTerm {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (τ z : ℤ → ℂ) (a : Coeff p) (n m : ℤ) : ℂ :=
  if m = n then 0 else
    a m/(τ m-z n)-a m/((Real.pi : ℂ)*m-z n)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An abstract form of the physical and free lattice separation assumptions. -/
def SeparatedReciprocalRows (S : Set ℤ) (C R : ℝ)
    (τ z : ℤ → ℂ) : Prop :=
  0 ≤ R ∧ 0 < C ∧
  (∀ m, ‖τ m-(Real.pi : ℂ)*m‖ ≤ R) ∧
  (∀ n ∈ S, ∀ m : ℤ, m ≠ n →
    |((n-m : ℤ) : ℝ)| ≤ C*‖τ m-z n‖) ∧
  (∀ n ∈ S, ∀ m : ℤ, m ≠ n →
    |((n-m : ℤ) : ℝ)| ≤ ‖(Real.pi : ℂ)*m-z n‖)

/-- The physical-to-free correction is bounded termwise by the square kernel. -/
theorem norm_separatedReciprocalTerm_le
    {S : Set ℤ} {C R : ℝ} {τ z : ℤ → ℂ}
    (h : SeparatedReciprocalRows S C R τ z)
    (a : Coeff p) {n : ℤ} (hn : n ∈ S) (m : ℤ) :
    ‖separatedReciprocalTerm τ z a n m‖ ≤
      C*R*‖a m‖*‖hilbertSquareCoeffs (n-m)‖ := by
  by_cases hmn : m = n
  · subst m
    simp [separatedReciprocalTerm, hilbertSquareCoeffs_apply,
      hilbertKernel]
  have hd : 0 < |((n-m : ℤ) : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast sub_ne_zero.mpr (Ne.symm hmn)
  have hnorm : ‖hilbertSquareCoeffs (n-m)‖ =
      |((n-m : ℤ) : ℝ)|⁻¹^2 := by
    simp only [hilbertSquareCoeffs_apply, hilbertKernel, norm_pow,
      norm_neg, norm_inv, Complex.norm_intCast]
  rw [separatedReciprocalTerm, if_neg hmn, hnorm]
  have hdiff : ‖(τ m-z n)-((Real.pi : ℂ)*m-z n)‖ ≤ R := by
    simpa only [sub_sub_sub_cancel_right] using h.2.2.1 m
  exact norm_div_sub_div_le_of_separation C R _ h.2.1.le h.1 hd
    (a m) (τ m-z n) ((Real.pi : ℂ)*m-z n)
    (h.2.2.2.1 n hn m hmn) (h.2.2.2.2 n hn m hmn) hdiff

/-- Every separated correction row is absolutely summable. -/
theorem summable_norm_separatedReciprocalTerm
    {S : Set ℤ} {C R : ℝ} {τ z : ℤ → ℂ}
    (h : SeparatedReciprocalRows S C R τ z)
    (a : Coeff p) {n : ℤ} (hn : n ∈ S) :
    Summable (fun m : ℤ => ‖separatedReciprocalTerm τ z a n m‖) := by
  have hbase := summable_hilbertSquareMajorant_row a n
  have hscaled : Summable (fun m : ℤ =>
      C*R*(‖a m‖*‖hilbertSquareCoeffs (n-m)‖)) :=
    hbase.mul_left (C*R)
  apply hscaled.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro m
  simpa only [mul_assoc] using norm_separatedReciprocalTerm_le h a hn m

/-- The physical-to-free correction, restricted to separated rows. -/
def separatedReciprocalCorrection
    {S : Set ℤ} {C R : ℝ} {τ z : ℤ → ℂ}
    (h : SeparatedReciprocalRows S C R τ z)
    (a : Coeff p) : Coeff p := by
  classical
  exact
  ⟨fun n => if hn : n ∈ S then ∑' m : ℤ, separatedReciprocalTerm τ z a n m else 0,
    by
      have hpoint (n : ℤ) :
          ‖(if hn : n ∈ S then ∑' m : ℤ, separatedReciprocalTerm τ z a n m else 0)‖ ≤
            C*R*‖hilbertSquareMajorant a n‖ := by
        split_ifs with hn
        · rw [norm_hilbertSquareMajorant_apply]
          have hsum := summable_norm_separatedReciprocalTerm h a hn
          calc
            ‖∑' m : ℤ, separatedReciprocalTerm τ z a n m‖ ≤
                ∑' m : ℤ, ‖separatedReciprocalTerm τ z a n m‖ :=
              norm_tsum_le_tsum_norm hsum
            _ ≤ ∑' m : ℤ, C*R*(‖a m‖*‖hilbertSquareCoeffs (n-m)‖) :=
              hsum.tsum_le_tsum (fun m => by simpa only [mul_assoc] using
                norm_separatedReciprocalTerm_le h a hn m)
                ((summable_hilbertSquareMajorant_row a n).mul_left (C*R))
            _ = C*R*∑' m : ℤ, ‖a m‖*‖hilbertSquareCoeffs (n-m)‖ := by
              rw [tsum_mul_left]
        · simp [mul_nonneg, h.2.1.le, h.1]
      apply ((lp.memℓp (hilbertSquareMajorant a)).const_mul ((C*R : ℝ) : ℂ)).mono'
      intro n
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg h.2.1.le, abs_of_nonneg h.1] using hpoint n⟩

@[simp] theorem separatedReciprocalCorrection_apply
    {S : Set ℤ} {C R : ℝ} {τ z : ℤ → ℂ}
    (h : SeparatedReciprocalRows S C R τ z)
    (a : Coeff p) {n : ℤ} (hn : n ∈ S) :
    separatedReciprocalCorrection h a n =
      ∑' m : ℤ, separatedReciprocalTerm τ z a n m := by
  classical
  simp [separatedReciprocalCorrection, hn]

/-- The `ℓp` norm of the full row correction is uniform in the samples. -/
theorem norm_separatedReciprocalCorrection_le
    {S : Set ℤ} {C R : ℝ} {τ z : ℤ → ℂ}
    (h : SeparatedReciprocalRows S C R τ z)
    (a : Coeff p) :
    ‖separatedReciprocalCorrection h a‖ ≤
      C*R*(‖a‖*‖hilbertSquareCoeffs‖) := by
  have hpoint (n : ℤ) :
      ‖separatedReciprocalCorrection h a n‖ ≤
        ‖((C*R : ℝ) : ℂ) • hilbertSquareMajorant a n‖ := by
    classical
    by_cases hn : n ∈ S
    · rw [separatedReciprocalCorrection_apply h a hn]
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg h.2.1.le h.1)]
      rw [norm_hilbertSquareMajorant_apply]
      have hsum := summable_norm_separatedReciprocalTerm h a hn
      calc
        ‖∑' m : ℤ, separatedReciprocalTerm τ z a n m‖ ≤
            ∑' m : ℤ, ‖separatedReciprocalTerm τ z a n m‖ :=
          norm_tsum_le_tsum_norm hsum
        _ ≤ ∑' m : ℤ, C*R*(‖a m‖*‖hilbertSquareCoeffs (n-m)‖) :=
          hsum.tsum_le_tsum (fun m => by simpa only [mul_assoc] using
            norm_separatedReciprocalTerm_le h a hn m)
            ((summable_hilbertSquareMajorant_row a n).mul_left (C*R))
        _ = _ := by rw [tsum_mul_left]
    · simp [separatedReciprocalCorrection, hn]
      positivity
  calc
    ‖separatedReciprocalCorrection h a‖ ≤
        ‖((C*R : ℝ) : ℂ) • hilbertSquareMajorant a‖ :=
      lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hpoint
    _ = C*R*‖hilbertSquareMajorant a‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg h.2.1.le h.1)]
    _ ≤ C*R*(‖a‖*‖hilbertSquareCoeffs‖) :=
      mul_le_mul_of_nonneg_left (norm_hilbertSquareMajorant_le a)
        (mul_nonneg h.2.1.le h.1)

end NLS.Fourier
