import NLS.SequenceSpaces.IteratedRowTesting
import NLS.ZakharovShabat.DoubleReciprocalSums
import NLS.SequenceSpaces.SpectralReflection

/-!
# Weighted two-index testing for the off-diagonal coefficient

Submultiplicativity transfers `w(2n)` to the two potential coefficients and
the shifted input. Hölder then retains the exact double reciprocal row norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.SpectralWeight
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The outer potential, in the normalized reciprocal index. -/
def doubleOuterCoeffs (w : SpectralWeight) (n : ℤ) (d : WeightedCoeff w.toWeight p) : Coeff p :=
  Coeff.reindex (Equiv.subLeft (2*n)) (WeightedCoeff.weightEquiv w.toWeight p d)

@[simp] theorem doubleOuterCoeffs_apply (w : SpectralWeight) (n : ℤ)
    (d : WeightedCoeff w.toWeight p) (j : ℤ) :
    w.doubleOuterCoeffs n d j = (w (2*n-j) : ℂ) * d.val (2*n-j) := rfl

theorem norm_doubleOuterCoeffs (w : SpectralWeight) (n : ℤ) (d : WeightedCoeff w.toWeight p) :
    ‖w.doubleOuterCoeffs n d‖ = ‖d‖ := by
  rw [doubleOuterCoeffs, Coeff.norm_reindex, ← WeightedCoeff.norm_eq]

/-- The input vector coefficient carries precisely the source shift `n`. -/
def doubleInputCoeffs (w : SpectralWeight) (n : ℤ) (f : WeightedCoeff w.toWeight p) : Coeff p :=
  Coeff.reindex (Equiv.subLeft n) (WeightedCoeff.weightEquiv (w.toWeight.shift n) p (w.toShift n f))

@[simp] theorem doubleInputCoeffs_apply (w : SpectralWeight) (n : ℤ)
    (f : WeightedCoeff w.toWeight p) (k : ℤ) :
    w.doubleInputCoeffs n f k = (w (2*n-k) : ℂ) * f.val (n-k) := by
  simp only [doubleInputCoeffs, Coeff.reindex_apply, WeightedCoeff.weightEquiv_apply,
    toShift_apply, Weight.shift_apply]
  change (w ((n-k)+n) : ℂ) * f.val (n-k) = _
  rw [show (n-k)+n = 2*n-k by ring]

theorem norm_doubleInputCoeffs (w : SpectralWeight) (n : ℤ) (f : WeightedCoeff w.toWeight p) :
    ‖w.doubleInputCoeffs n f‖ = w.shiftedNorm n f := by
  rw [doubleInputCoeffs, Coeff.norm_reindex, ← WeightedCoeff.norm_eq]
  rfl

/-- The output weight transfers to all three Fourier factors with constant one. -/
theorem double_index_weight_le (w : SpectralWeight) (n j k : ℤ) :
    w (2*n) ≤ w (2*n-j) * w (2*n-j-k) * w (2*n-k) := by
  calc
    _ = w ((2*n-j) + (-(2*n-j-k)) + (2*n-k)) := by congr 1; ring
    _ ≤ w ((2*n-j) + (-(2*n-j-k))) * w (2*n-k) := w.add_le _ _
    _ ≤ (w (2*n-j) * w (-(2*n-j-k))) * w (2*n-k) :=
      mul_le_mul_of_nonneg_right (w.add_le _ _) (w.positive _).le
    _ = _ := by rw [w.apply_neg]

end NLS.SpectralWeight
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

omit [Fact (1 ≤ q)] in
/-- A reciprocal denominator in normalized coordinates is bounded by the punctured lattice. -/
theorem norm_complementarySymbol_centered_le (hq : 1 < q) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (j : ℤ) :
    ‖complementarySymbol n z (n-j)‖ ≤ ‖Coeff.puncturedLattice q hq j‖ := by
  have h := norm_complementarySymbol_le_lattice hq hz (n-j)
  rw [show (n-j)-n = -j by ring] at h
  simpa only [norm_puncturedLattice_eq_inv_abs, Int.cast_neg, abs_neg] using h

/-- The weighted source double-series term in normalized reciprocal coordinates. -/
def weightedOffDiagonalTerm (w : SpectralWeight) (d a f : WeightedCoeff w.toWeight p)
    (n : ℤ) (z : ℂ) (j k : ℤ) : ℂ :=
  (w (2*n) : ℂ) * d.val (2*n-j) * a.val (2*n-j-k) *
    complementarySymbol n z (n-j) * complementarySymbol n z (n-k) * f.val (n-k)

omit [Fact (1 ≤ q)] in
/-- Pointwise domination transfers all weights and both denominators to the Hölder test. -/
theorem norm_weightedOffDiagonalTerm_le (hq : 1 < q) (w : SpectralWeight)
    (d a f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (j k : ℤ) :
    ‖weightedOffDiagonalTerm w d a f n z j k‖ ≤
      ‖w.doubleOuterCoeffs n d j * WeightedCoeff.weightEquiv w.toWeight p a (2*n-j-k) *
        Coeff.puncturedLattice q hq k * Coeff.puncturedLattice q hq j * w.doubleInputCoeffs n f k‖ := by
  simp only [weightedOffDiagonalTerm, SpectralWeight.doubleOuterCoeffs_apply,
    SpectralWeight.doubleInputCoeffs_apply, WeightedCoeff.weightEquiv_apply,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg (w.positive _).le]
  calc
    _ ≤ (w (2*n-j) * w (2*n-j-k) * w (2*n-k)) * ‖d.val (2*n-j)‖ * ‖a.val (2*n-j-k)‖ *
        ‖Coeff.puncturedLattice q hq j‖ * ‖Coeff.puncturedLattice q hq k‖ * ‖f.val (n-k)‖ := by
      have hw₁ := (w.positive (2*n-j)).le
      have hw₂ := (w.positive (2*n-j-k)).le
      have hw₃ := (w.positive (2*n-k)).le
      gcongr
      · exact w.double_index_weight_le n j k
      · exact norm_complementarySymbol_centered_le hq n z hz j
      · exact norm_complementarySymbol_centered_le hq n z hz k
    _ = _ := by ring

/-- The weighted double Fourier series is absolutely convergent on the product index set. -/
theorem summable_norm_weightedOffDiagonalTerm [p.HolderConjugate q] (hq : 1 < q)
    (w : SpectralWeight) (d a f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    Summable (fun jk : ℤ × ℤ => ‖weightedOffDiagonalTerm w d a f n z jk.1 jk.2‖) := by
  exact (Coeff.summable_iteratedRowTest_prod (WeightedCoeff.weightEquiv w.toWeight p a)
    (w.doubleOuterCoeffs n d) (w.doubleInputCoeffs n f) (Coeff.puncturedLattice q hq)
    (Coeff.puncturedLattice q hq) (2*n)).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun jk => norm_weightedOffDiagonalTerm_le hq w d a f n z hz jk.1 jk.2)

/-- The weighted version of the two-index Hölder bound, retaining the exact shifted input norm. -/
theorem norm_tsum_weightedOffDiagonalTerm_le [p.HolderConjugate q] (hq : 1 < q)
    (w : SpectralWeight) (d a f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖∑' j : ℤ, ∑' k : ℤ, weightedOffDiagonalTerm w d a f n z j k‖ ≤
      ‖d‖ * w.shiftedNorm n f * ‖doubleReciprocalRow hq (WeightedCoeff.weightEquiv w.toWeight p a) n‖ := by
  have h := summable_norm_weightedOffDiagonalTerm hq w d a f n z hz
  have ht := Coeff.summable_iteratedRowTest_prod (WeightedCoeff.weightEquiv w.toWeight p a)
    (w.doubleOuterCoeffs n d) (w.doubleInputCoeffs n f) (Coeff.puncturedLattice q hq)
    (Coeff.puncturedLattice q hq) (2*n)
  calc
    _ = ‖∑' jk : ℤ × ℤ, weightedOffDiagonalTerm w d a f n z jk.1 jk.2‖ := by rw [h.of_norm.tsum_prod]
    _ ≤ ∑' jk : ℤ × ℤ, ‖weightedOffDiagonalTerm w d a f n z jk.1 jk.2‖ := norm_tsum_le_tsum_norm h
    _ ≤ ∑' jk : ℤ × ℤ, ‖w.doubleOuterCoeffs n d jk.1 * WeightedCoeff.weightEquiv w.toWeight p a (2*n-jk.1-jk.2) *
        Coeff.puncturedLattice q hq jk.2 * Coeff.puncturedLattice q hq jk.1 * w.doubleInputCoeffs n f jk.2‖ :=
      h.tsum_le_tsum (fun jk => norm_weightedOffDiagonalTerm_le hq w d a f n z hz jk.1 jk.2) ht
    _ ≤ ‖w.doubleOuterCoeffs n d‖ * ‖w.doubleInputCoeffs n f‖ *
        ‖Coeff.iteratedConvolutionRow (WeightedCoeff.weightEquiv w.toWeight p a)
          (Coeff.puncturedLattice q hq) (Coeff.puncturedLattice q hq) (2*n)‖ := by
      rw [ht.tsum_prod]
      exact Coeff.tsum_norm_iteratedRowTest_le _ _ _ _ _ _
    _ = _ := by rw [w.norm_doubleOuterCoeffs, w.norm_doubleInputCoeffs]; rfl

end NLS.ZakharovShabat
