import NLS.SequenceSpaces.IteratedConvolutionRows
import NLS.SequenceSpaces.ConjugateDuality
import NLS.SequenceSpaces.SandwichMajorant

/-!
# Two-index Hölder testing

The iterated reciprocal row is tested against one outer potential sequence
and one inner vector sequence. Absolute convergence is proved on the product
index set before identifying the nested Fourier sum.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The sum of absolute products satisfies the same Hölder bound as coefficient duality. -/
theorem tsum_norm_dualPairing_le (a : Coeff p) (b : Coeff q) :
    (∑' k : ℤ, ‖a k * b k‖) ≤ ‖a‖ * ‖b‖ := by
  have h := norm_dualPairing_le (magnitude a) (magnitude b)
  simpa only [dualPairing_apply, magnitude_apply, ← Complex.ofReal_mul,
    ← Complex.ofReal_tsum, Complex.norm_real,
    Real.norm_of_nonneg (tsum_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))),
    norm_magnitude, norm_mul] using h

/-- Each inner absolute row converges before the outer Hölder estimate is applied. -/
theorem summable_iteratedRowTest_inner (a d f : Coeff p) (b c : Coeff q) (m j : ℤ) :
    Summable (fun k : ℤ => ‖d j * a (m-j-k) * c k * b j * f k‖) := by
  have h := (summable_norm_dualPairing f (convolutionRow a c (m-j))).mul_left (‖d j‖*‖b j‖)
  apply h.congr
  intro k
  simp only [convolutionRow_apply, norm_mul]
  ring

/-- The inner Hölder bound retains the exact outer reciprocal-row coefficient. -/
theorem tsum_iteratedRowTest_inner_le (a d f : Coeff p) (b c : Coeff q) (m j : ℤ) :
    (∑' k : ℤ, ‖d j * a (m-j-k) * c k * b j * f k‖) ≤
      ‖f‖ * ‖d j * iteratedConvolutionRow a b c m j‖ := by
  have he : (∑' k : ℤ, ‖d j * a (m-j-k) * c k * b j * f k‖) =
      (‖d j‖*‖b j‖) * ∑' k : ℤ, ‖f k * convolutionRow a c (m-j) k‖ := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    simp only [norm_mul, convolutionRow_apply]
    ring
  rw [he]
  calc
    _ ≤ (‖d j‖*‖b j‖) * (‖f‖ * ‖convolutionRow a c (m-j)‖) :=
      mul_le_mul_of_nonneg_left (tsum_norm_dualPairing_le f _) (by positivity)
    _ = _ := by
      simp only [iteratedConvolutionRow_apply, norm_mul, Complex.norm_real, norm_norm]
      ring

/-- The complete absolute double Fourier sum converges jointly. -/
theorem summable_iteratedRowTest_prod (a d f : Coeff p) (b c : Coeff q) (m : ℤ) :
    Summable (fun jk : ℤ × ℤ => ‖d jk.1 * a (m-jk.1-jk.2) * c jk.2 * b jk.1 * f jk.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨summable_iteratedRowTest_inner a d f b c m, ?_⟩
  exact ((summable_norm_dualPairing d (iteratedConvolutionRow a b c m)).mul_left ‖f‖).of_nonneg_of_le
    (fun _ => tsum_nonneg (fun _ => norm_nonneg _)) (tsum_iteratedRowTest_inner_le a d f b c m)

/-- Two successive Hölder inequalities bound the absolute double sum with constant one. -/
theorem tsum_norm_iteratedRowTest_le (a d f : Coeff p) (b c : Coeff q) (m : ℤ) :
    (∑' j : ℤ, ∑' k : ℤ, ‖d j * a (m-j-k) * c k * b j * f k‖) ≤
      ‖d‖ * ‖f‖ * ‖iteratedConvolutionRow a b c m‖ := by
  calc
    _ ≤ ∑' j : ℤ, ‖f‖ * ‖d j * iteratedConvolutionRow a b c m j‖ :=
      (summable_iteratedRowTest_prod a d f b c m).prod.tsum_le_tsum
        (tsum_iteratedRowTest_inner_le a d f b c m)
        ((summable_norm_dualPairing d (iteratedConvolutionRow a b c m)).mul_left ‖f‖)
    _ = ‖f‖ * ∑' j : ℤ, ‖d j * iteratedConvolutionRow a b c m j‖ := tsum_mul_left
    _ ≤ ‖f‖ * (‖d‖ * ‖iteratedConvolutionRow a b c m‖) :=
      mul_le_mul_of_nonneg_left (tsum_norm_dualPairing_le d _) (norm_nonneg _)
    _ = _ := by ring

/-- The actual complex double series has the same bound and no rearrangement ambiguity. -/
theorem norm_tsum_iteratedRowTest_le (a d f : Coeff p) (b c : Coeff q) (m : ℤ) :
    ‖∑' j : ℤ, ∑' k : ℤ, d j * a (m-j-k) * c k * b j * f k‖ ≤
      ‖d‖ * ‖f‖ * ‖iteratedConvolutionRow a b c m‖ := by
  have h := summable_iteratedRowTest_prod a d f b c m
  calc
    _ = ‖∑' jk : ℤ × ℤ, d jk.1 * a (m-jk.1-jk.2) * c jk.2 * b jk.1 * f jk.2‖ := by
      rw [h.of_norm.tsum_prod]
    _ ≤ ∑' jk : ℤ × ℤ, ‖d jk.1 * a (m-jk.1-jk.2) * c jk.2 * b jk.1 * f jk.2‖ := norm_tsum_le_tsum_norm h
    _ = ∑' j : ℤ, ∑' k : ℤ, ‖d j * a (m-j-k) * c k * b j * f k‖ := h.tsum_prod
    _ ≤ _ := tsum_norm_iteratedRowTest_le a d f b c m

end NLS.Coeff
