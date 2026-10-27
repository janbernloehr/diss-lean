import NLS.ZakharovShabat.SourceFreeResolvent

/-! # Corrections to the p=1 proof bounds in Lemma 3.2

On printed p. 24, both endpoint reciprocal-supremum inequalities point
in the wrong direction. The actual symbol satisfies upper bounds by
1/|Im z| and 1/r. Pure imaginary parameters give exact supremum and
original component-sum operator norms, and refute the printed lower bounds.
These corrections are separate from the missing pair factor in clause (ii).
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The literal scalar supremum in the two p=1 sentences of the proof. -/
def freeReciprocalSup (z : ℂ) : ℝ :=
  ⨆ m : ℤ, 1 / ‖z - (Real.pi : ℂ) * m‖

/-- The p=1 Hölder symbol norm is precisely the printed scalar supremum. -/
theorem scalarFreeL1Bound_one_eq_reciprocalSup (z : ℂ) (hz : z ∉ freeLattice) :
    scalarFreeL1Bound 1 (by simp) z hz = freeReciprocalSup z := by
  have hnorm {q : ℝ≥0∞} (hq : q = ⊤) (a : Coeff q) :
      ‖a‖ = ⨆ m : ℤ, ‖a m‖ := by
    subst q
    exact lp.norm_eq_ciSup a
  rw [scalarFreeL1Bound, hnorm (by simp [ENNReal.conjExponent])]
  change (⨆ m : ℤ, ‖(z - (Real.pi : ℂ) * m)⁻¹‖) = freeReciprocalSup z
  simp only [freeReciprocalSup, one_div, norm_inv]

/-- Corrected height estimate, sharper than the printed sqrt(2) constant. -/
theorem freeReciprocalSup_le_height {z : ℂ} (him : z.im ≠ 0) :
    freeReciprocalSup z ≤ 1 / |z.im| := by
  rw [← scalarFreeL1Bound_one_eq_reciprocalSup z
    (notMem_freeLattice_of_im_ne_zero him)]
  simpa only [one_div] using
    scalarFreeL1Bound_one_le z (notMem_freeLattice_of_im_ne_zero him) him

/-- Corrected punctured-strip estimate, including real spectral parameters. -/
theorem freeReciprocalSup_le_verticalStrip {n : ℤ} {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    freeReciprocalSup z ≤ 1 / r := by
  apply ciSup_le
  intro m
  have h := verticalStrip_denominator_lower (m := m) hr hrπ hz
  have hd : r ≤ ‖z - (Real.pi : ℂ) * m‖ := by
    nlinarith [abs_nonneg (((m - n : ℤ) : ℝ))]
  exact one_div_le_one_div_of_le hr hd

/-- At a nonzero imaginary parameter the zero Fourier mode attains the supremum. -/
theorem freeReciprocalSup_pureImaginary (y : ℝ) (hy : y ≠ 0) :
    freeReciprocalSup ((y : ℂ) * Complex.I) = 1 / |y| := by
  have him : ((y : ℂ) * Complex.I).im ≠ 0 := by simpa using hy
  apply le_antisymm
  · simpa using freeReciprocalSup_le_height him
  · have hb : BddAbove (Set.range (fun m : ℤ =>
        1 / ‖(y : ℂ) * Complex.I - (Real.pi : ℂ) * m‖)) := by
      refine ⟨1 / |y|, ?_⟩
      rintro _ ⟨m,rfl⟩
      have hd : |y| ≤ ‖(y : ℂ) * Complex.I - (Real.pi : ℂ) * m‖ := by
        simpa using Complex.abs_im_le_norm
          ((y : ℂ) * Complex.I - (Real.pi : ℂ) * m)
      exact one_div_le_one_div_of_le (abs_pos.mpr hy) hd
    simpa [freeReciprocalSup, norm_mul] using le_ciSup hb (0 : ℤ)

/-- The same sharp bound holds for the actual original-norm p=1 pair resolvent. -/
theorem norm_sourceFreeResolventToL1_one_le_im {z : ℂ} (him : z.im ≠ 0) :
    ‖sourceFreeResolventToL1 (by simp : (1 : ℝ≥0∞) ≠ ⊤)
      z (notMem_freeLattice_of_im_ne_zero him)‖ ≤ 1 / |z.im| := by
  apply (norm_sourceFreeResolventToL1_le (by simp) z _).trans
  simpa only [CoeffPair.l1Factor_one, one_mul, one_div] using
    freeL1Bound_one_le z (notMem_freeLattice_of_im_ne_zero him) him

/-- Original-norm endpoint resolvents satisfy the corrected strip estimate. -/
theorem norm_sourceFreeResolventToL1_one_le_strip {n : ℤ} {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    ‖sourceFreeResolventToL1 (by simp : (1 : ℝ≥0∞) ≠ ⊤)
      z (notMem_freeLattice_of_mem_verticalStrip hr hrπ hz)‖ ≤ 1 / r := by
  apply (norm_sourceFreeResolventToL1_le (by simp) z _).trans
  simp only [CoeffPair.l1Factor_one, one_mul, freeL1Bound,
    scalarFreeL1Bound_one_eq_reciprocalSup]
  exact max_le (freeReciprocalSup_le_verticalStrip hr hrπ (neg_mem_verticalStrip hz))
    (freeReciprocalSup_le_verticalStrip hr hrπ hz)

/-- Both zero components attain the exact original p=1 operator norm. -/
theorem norm_sourceFreeResolventToL1_one_pureImaginary (y : ℝ) (hy : y ≠ 0) :
    ‖sourceFreeResolventToL1 (by simp : (1 : ℝ≥0∞) ≠ ⊤)
      ((y : ℂ) * Complex.I)
      (notMem_freeLattice_of_im_ne_zero (by simpa using hy))‖ = 1 / |y| := by
  apply le_antisymm
  · simpa using norm_sourceFreeResolventToL1_one_le_im
      (z := (y : ℂ) * Complex.I) (by simpa using hy)
  · simpa [CoeffPair.l1Factor_one, norm_mul] using
      l1Factor_div_norm_le_sourceFreeResolventToL1
        (by simp : (1 : ℝ≥0∞) ≠ ⊤) ((y : ℂ) * Complex.I)
        (notMem_freeLattice_of_im_ne_zero (by simpa using hy))

/-- The first printed p=1 lower bound is false at the actual parameter i. -/
theorem lemma3_2_proof_height_lower_bound_false :
    ¬ Real.sqrt 2 / |Complex.I.im| ≤ freeReciprocalSup Complex.I := by
  have he := freeReciprocalSup_pureImaginary 1 (by norm_num)
  simp only [Complex.ofReal_one, one_mul, abs_one, div_one] at he
  rw [he]
  simp only [Complex.I_im, abs_one, div_one]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

/-- The second printed lower bound fails inside its stated punctured strip. -/
theorem lemma3_2_proof_strip_lower_bound_false :
    0 < Real.pi / 4 ∧ Real.pi / 4 ≤ Real.pi / 4 ∧
      (Real.pi : ℂ) * Complex.I ∈ verticalStrip 0 (Real.pi / 4) ∧
      ¬ 1 / (Real.pi / 4) ≤ freeReciprocalSup ((Real.pi : ℂ) * Complex.I) := by
  refine ⟨by positivity, le_rfl, ?_, ?_⟩
  · constructor
    · simpa using (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    · simp only [Int.cast_zero, mul_zero, sub_zero, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
      linarith [Real.pi_pos]
  · rw [freeReciprocalSup_pureImaginary Real.pi Real.pi_ne_zero,
      abs_of_pos Real.pi_pos]
    exact not_le_of_gt (one_div_lt_one_div_of_lt (by positivity)
      (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi))

end NLS.ZakharovShabat
