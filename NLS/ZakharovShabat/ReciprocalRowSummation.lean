import NLS.ZakharovShabat.ComplementaryRowEstimate
import NLS.SequenceSpaces.ConvolutionRowTails

/-!
# Summation of the reciprocal row majorants

The physical reciprocal row norm is a convolution row sampled at `2n`.
For any auxiliary exponent `1<r≤min(p,q)`, powered Young and exponent
inclusion supply an outer `ℓ^p` majorant, including a quantitative two-tail bound.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- Signed reciprocal rows have exactly the norm of the convolution row at twice the frequency. -/
theorem norm_complementaryRowEnvelope_eq_convolutionRow (hq : 1 < q) (a : Coeff p) (n : ℤ) :
    ‖complementaryRowEnvelope hq a n‖ = ‖Coeff.convolutionRow a (Coeff.puncturedLattice q hq) (2*n)‖ := by
  rw [← Coeff.norm_reindex (Equiv.addRight n) (Coeff.convolutionRow a (Coeff.puncturedLattice q hq) (2*n))]
  have he (k : ℤ) : ‖complementaryRowEnvelope hq a n k‖ =
      ‖Coeff.reindex (Equiv.addRight n) (Coeff.convolutionRow a (Coeff.puncturedLattice q hq) (2*n)) k‖ := by
    change ‖a (n-k) * Coeff.puncturedLattice q hq (-k-n)‖ =
      ‖a (2*n-(k+n)) * Coeff.puncturedLattice q hq (k+n)‖
    rw [show 2*n-(k+n) = n-k by ring, show -k-n = -(k+n) by ring]
    rw [norm_mul, norm_mul]
    congr 1
    by_cases hkn : k+n = 0
    · simp [hkn]
    · simp only [Coeff.puncturedLattice_apply, if_neg hkn, if_neg (neg_ne_zero.mpr hkn),
        Int.cast_neg, norm_inv, norm_neg]
  apply le_antisymm <;> apply lp.norm_mono (zero_lt_one.trans hq).ne' <;> intro k
  · exact (he k).le
  · exact (he k).ge

/-- The same reciprocal sequence embeds contractively into every larger exponent. -/
theorem exponentInclusion_puncturedLattice (hr : 1 < r) (hrq : r ≤ q) :
    Coeff.exponentInclusion hrq (Coeff.puncturedLattice r hr) = Coeff.puncturedLattice q (hr.trans_le hrq) := by
  ext k
  rfl

/-- A smaller inner exponent bounds the original reciprocal row norm. -/
theorem norm_complementaryRowEnvelope_le_inner (hr : 1 < r) (hrq : r ≤ q) (a : Coeff p) (n : ℤ) :
    ‖complementaryRowEnvelope (hr.trans_le hrq) a n‖ ≤
      ‖Coeff.convolutionRow a (Coeff.puncturedLattice r hr) (2*n)‖ := by
  rw [norm_complementaryRowEnvelope_eq_convolutionRow, ← exponentInclusion_puncturedLattice hr hrq]
  exact Coeff.norm_convolutionRow_exponent_le hrq a _ (2*n)

/-- Reciprocal row norms have an actual outer `ℓ^p` majorant. -/
theorem exists_reciprocalRowMajorant (hp : p ≠ ⊤) (hr : 1 < r) (hrp : r ≤ p) (hrq : r ≤ q)
    (a : Coeff p) :
    ∃ d : Coeff p,
      (∀ n : ℤ, ‖complementaryRowEnvelope (hr.trans_le hrq) a n‖ ≤ ‖d n‖) ∧
      ‖d‖ ≤ ‖a‖ * ‖Coeff.puncturedLattice r hr‖ := by
  obtain ⟨d, hd, hn⟩ := Coeff.exists_evenConvolutionRowNorm hp hrp a (Coeff.puncturedLattice r hr)
  refine ⟨d, ?_, hn⟩
  intro n
  rw [hd, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_complementaryRowEnvelope_le_inner hr hrq a n

/-- The tail estimate retains both the reciprocal tail and the actual potential tail. -/
theorem exists_reciprocalRowTailMajorant (hp : p ≠ ⊤) (hr : 1 < r) (hrp : r ≤ p) (hrq : r ≤ q)
    (a : Coeff p) (N : ℕ) :
    ∃ d : Coeff p,
      (∀ n : ℤ, N ≤ n.natAbs → ‖complementaryRowEnvelope (hr.trans_le hrq) a n‖ ≤ ‖d n‖) ∧
      ‖d‖ ≤ ‖a‖ * ‖Coeff.fourierTail N (Coeff.puncturedLattice r hr)‖ +
        ‖Coeff.fourierTail N a‖ * ‖Coeff.puncturedLattice r hr‖ := by
  obtain ⟨d, hd, hn⟩ := Coeff.exists_evenConvolutionRowTailMajorant hp hrp a (Coeff.puncturedLattice r hr) N
  exact ⟨d, fun n hn => (norm_complementaryRowEnvelope_le_inner hr hrq a n).trans (hd n hn), hn⟩

end NLS.ZakharovShabat
