import NLS.SequenceSpaces.ExponentialSpectralWeights

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Fourier

/-- The exact physical Fourier multiplier for the horizontal line at height y,
including the source's pi-scaled Sobolev factor at even frequency 2n. -/
def abelBoundaryCoefficient (s y : ℝ) (c : ℤ → ℂ) (n : ℤ) : ℂ :=
  (((1+|((2*n:ℤ):ℝ)*Real.pi|)^s:ℝ):ℂ)*
    (Real.exp (-2*Real.pi*y*(n:ℝ)):ℂ)*c n

/-- The boundary norm keeps both the physical Sobolev and horizontal-shift factors. -/
theorem norm_abelBoundaryCoefficient (s y : ℝ) (c : ℤ → ℂ) (n : ℤ) :
    ‖abelBoundaryCoefficient s y c n‖ =
      (1+|((2*n:ℤ):ℝ)*Real.pi|)^s*Real.exp (-2*Real.pi*y*(n:ℝ))*‖c n‖ := by
  have hp : (0:ℝ) < 1+|((2*n:ℤ):ℝ)*Real.pi| := by positivity
  simp only [abelBoundaryCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hp s),Real.abs_exp]

/-- The exact coefficient bound holds throughout the corrected closed strip a/pi. -/
theorem norm_abelBoundaryCoefficient_le (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (y : ℝ) (hy : |y| ≤ a/Real.pi) (c : ℤ → ℂ) (n : ℤ) :
    ‖abelBoundaryCoefficient s y c n‖ ≤
      ‖(SpectralWeight.abel s a hs ha (2*n):ℂ)*c n‖ := by
  have hb : Real.pi*|y| ≤ a := by
    have h := (le_div_iff₀ Real.pi_pos).mp hy
    nlinarith
  have hexp : -2*Real.pi*y*(n:ℝ) ≤ a*|((2*n:ℤ):ℝ)| := by
    have ht := neg_le_abs (2*Real.pi*y*(n:ℝ))
    have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg (n:ℝ))
    simp only [abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
    simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith
  rw [norm_abelBoundaryCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos ((SpectralWeight.abel s a hs ha).positive (2*n)),SpectralWeight.abel_apply]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (Real.rpow_nonneg (by positivity) s))
    (norm_nonneg _)

/-- The lower corrected boundary exactly recovers the weighted nonnegative modes. -/
theorem abel_weighted_eq_lower_boundary (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (c : ℤ → ℂ) (n : ℤ) (hn : 0 ≤ n) :
    (SpectralWeight.abel s a hs ha (2*n):ℂ)*c n = abelBoundaryCoefficient s (-a/Real.pi) c n := by
  have hnR : 0 ≤ (n:ℝ) := by exact_mod_cast hn
  have habs : |((2*n:ℤ):ℝ)| = 2*(n:ℝ) := by
    rw [Int.cast_mul,Int.cast_ofNat,abs_of_nonneg (by positivity)]
  have he : a*|((2*n:ℤ):ℝ)| = -2*Real.pi*(-a/Real.pi)*(n:ℝ) := by
    rw [habs]
    field_simp
  simp only [SpectralWeight.abel_apply,abelBoundaryCoefficient,Complex.ofReal_mul,he]

/-- The upper corrected boundary exactly recovers the weighted nonpositive modes. -/
theorem abel_weighted_eq_upper_boundary (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (c : ℤ → ℂ) (n : ℤ) (hn : n ≤ 0) :
    (SpectralWeight.abel s a hs ha (2*n):ℂ)*c n = abelBoundaryCoefficient s (a/Real.pi) c n := by
  have hnR : (n:ℝ) ≤ 0 := by exact_mod_cast hn
  have habs : |((2*n:ℤ):ℝ)| = -(2*(n:ℝ)) := by
    rw [Int.cast_mul,Int.cast_ofNat,abs_of_nonpos (by nlinarith)]
  have he : a*|((2*n:ℤ):ℝ)| = -2*Real.pi*(a/Real.pi)*(n:ℝ) := by
    rw [habs]
    field_simp
  simp only [SpectralWeight.abel_apply,abelBoundaryCoefficient,Complex.ofReal_mul,he]

/-- Abel membership controls every horizontal coefficient sequence in the corrected strip. -/
theorem memlp_abelBoundaryCoefficient (p : ℝ≥0∞) (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (c : ℤ → ℂ) (hc : Memℓp (fun n => (SpectralWeight.abel s a hs ha (2*n):ℂ)*c n) p)
    (y : ℝ) (hy : |y| ≤ a/Real.pi) : Memℓp (abelBoundaryCoefficient s y c) p :=
  hc.mono' (norm_abelBoundaryCoefficient_le s a hs ha y hy c)

/-- The literal Abel coefficient space is exactly the intersection of the two
corrected boundary coefficient spaces, including both signed tails and zero. -/
theorem memlp_abel_iff_boundary_coefficients (p : ℝ≥0∞)
    (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (c : ℤ → ℂ) :
    Memℓp (fun n => (SpectralWeight.abel s a hs ha (2*n):ℂ)*c n) p ↔
      Memℓp (abelBoundaryCoefficient s (a/Real.pi) c) p ∧
      Memℓp (abelBoundaryCoefficient s (-a/Real.pi) c) p := by
  have hu : |a/Real.pi| ≤ a/Real.pi := by rw [abs_of_nonneg (by positivity)]
  have hl : |-a/Real.pi| ≤ a/Real.pi := by rw [neg_div,abs_neg,abs_of_nonneg (by positivity)]
  constructor
  · intro hc
    exact ⟨memlp_abelBoundaryCoefficient p s a hs ha c hc _ hu,
      memlp_abelBoundaryCoefficient p s a hs ha c hc _ hl⟩
  · rintro ⟨hcU,hcL⟩
    apply (hcU.norm.add hcL.norm).mono
    intro n
    by_cases hn : 0 ≤ n
    · rw [abel_weighted_eq_lower_boundary s a hs ha c n hn]
      exact le_add_of_nonneg_left (norm_nonneg _)
    · rw [abel_weighted_eq_upper_boundary s a hs ha c n (le_of_lt (lt_of_not_ge hn))]
      exact le_add_of_nonneg_right (norm_nonneg _)

end NLS.Fourier
