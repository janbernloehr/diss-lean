import NLS.SequenceSpaces.FiniteInterpolation
import NLS.Fourier.HilbertDuality

/-!
# Interpolation of discrete Hilbert estimates

The finite kernel pairing satisfies the endpoint Hölder estimates. Three-lines
interpolation and finite conjugate norm detection give an intermediate estimate,
which is then completed using `HilbertEstimate`.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier

/-- The finite Hilbert pairing is the matrix pairing for the reciprocal kernel. -/
theorem kernelPair_hilbert (a b : ℤ →₀ ℂ) :
    Coeff.kernelPair (fun n k => ((k : ℂ)-n)⁻¹) a b =
      b.sum (fun n z => finiteHilbert a n * z) := by
  simp only [Coeff.kernelPair, finiteHilbert, Finsupp.sum, Finset.sum_mul, div_eq_mul_inv]
  rw [Finset.sum_comm]

/-- A Hilbert estimate supplies exactly the bilinear endpoint bound used in interpolation. -/
theorem HilbertEstimate.norm_kernelPair_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (h : HilbertEstimate p) (a b : ℤ →₀ ℂ) :
    ‖Coeff.kernelPair (fun n k => ((k : ℂ)-n)⁻¹) a b‖ ≤
      h.bound * ‖Coeff.ofFinsupp (p := p) a‖ * ‖Coeff.ofFinsupp (p := q) b‖ := by
  have he : Coeff.kernelPair (fun n k => ((k : ℂ)-n)⁻¹) a b =
      Coeff.dualPairing (h.operator (Coeff.ofFinsupp a)) (Coeff.ofFinsupp (p := q) b) := by
    rw [kernelPair_hilbert, Coeff.dualPairing_finite_right]
    simp only [h.operator_finite]
  rw [he]
  exact (Coeff.norm_dualPairing_le _ _).trans
    (mul_le_mul_of_nonneg_right (h.norm_operator_apply_le _) (norm_nonneg _))

/-- Conjugate reciprocal exponents interpolate with the same parameter. -/
theorem conjugate_interpolation_identity {p₀ p₁ q₀ q₁ r s t : ℝ}
    (h₀ : p₀.HolderConjugate q₀) (h₁ : p₁.HolderConjugate q₁)
    (h : r.HolderConjugate s) (ht : r * ((1-t)/p₀ + t/p₁) = 1) :
    s * ((1-t)/q₀ + t/q₁) = 1 := by
  have he : (1-t)/p₀ + t/p₁ = r⁻¹ := by
    apply (mul_left_cancel₀ h.ne_zero)
    rw [ht, mul_inv_cancel₀ h.ne_zero]
  simp only [div_eq_mul_inv]
  rw [← h₀.one_sub_inv, ← h₁.one_sub_inv]
  calc
    _ = s * (1 - ((1-t)/p₀ + t/p₁)) := by ring
    _ = s * s⁻¹ := by rw [he, h.one_sub_inv]
    _ = 1 := mul_inv_cancel₀ h.symm.ne_zero

/-- Interpolation first controls normalized finite inputs. -/
theorem norm_finiteHilbert_interpolate_unit {p₀ p₁ r : ℝ≥0∞}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ r)]
    (h₀ : HilbertEstimate p₀) (h₁ : HilbertEstimate p₁)
    (hr : 1 < r) (hrtop : r ≠ ⊤) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hrt : r.toReal * ((1-t)/p₀.toReal + t/p₁.toReal) = 1)
    (a : ℤ →₀ ℂ) (ha : ‖Coeff.ofFinsupp (p := r) a‖ ≤ 1) :
    ‖finiteHilbertCoeffs hr a‖ ≤ max h₀.bound h₁.bound := by
  let q₀ := p₀.conjExponent
  let q₁ := p₁.conjExponent
  let s := r.conjExponent
  let : Fact (1 ≤ q₀) := ⟨ENNReal.HolderConjugate.one_le q₀ p₀⟩
  let : Fact (1 ≤ q₁) := ⟨ENNReal.HolderConjugate.one_le q₁ p₁⟩
  let : Fact (1 ≤ s) := ⟨ENNReal.HolderConjugate.one_le s r⟩
  have hp₀ := ENNReal.toReal_pos (zero_lt_one.trans h₀.one_lt).ne' h₀.ne_top
  have hp₁ := ENNReal.toReal_pos (zero_lt_one.trans h₁.one_lt).ne' h₁.ne_top
  have hr' := ENNReal.toReal_pos (zero_lt_one.trans hr).ne' hrtop
  have hq₀top : q₀ ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q₀ p₀).mpr h₀.one_lt.ne'
  have hq₁top : q₁ ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q₁ p₁).mpr h₁.one_lt.ne'
  have hstop : s ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one s r).mpr hr.ne'
  have hq₀ := ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q₀ p₀) hq₀top
  have hq₁ := ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q₁ p₁) hq₁top
  have hs := ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero s r) hstop
  have hst := conjugate_interpolation_identity
    (ENNReal.HolderConjugate.toReal_of_ne_top h₀.ne_top hq₀top)
    (ENNReal.HolderConjugate.toReal_of_ne_top h₁.ne_top hq₁top)
    (ENNReal.HolderConjugate.toReal_of_ne_top hrtop hstop) hrt
  apply Coeff.norm_le_of_finite_dual_unit (q := s) hr' hs hrtop
  intro b hb
  simp only [finiteHilbertCoeffs_apply]
  rw [← kernelPair_hilbert]
  exact Coeff.norm_kernelPair_interpolate_unit hp₀ hp₁ hq₀ hq₁ hr' hs ht₀ ht₁ hrt hst
    _ h₀.bound_nonneg h₁.bound_nonneg h₀.norm_kernelPair_le h₁.norm_kernelPair_le a b ha hb

/-- Rescaling yields a support-independent estimate at the intermediate exponent. -/
theorem norm_finiteHilbert_interpolate_le {p₀ p₁ r : ℝ≥0∞}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ r)]
    (h₀ : HilbertEstimate p₀) (h₁ : HilbertEstimate p₁)
    (hr : 1 < r) (hrtop : r ≠ ⊤) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hrt : r.toReal * ((1-t)/p₀.toReal + t/p₁.toReal) = 1) (a : ℤ →₀ ℂ) :
    ‖finiteHilbertCoeffs hr a‖ ≤ max h₀.bound h₁.bound * ‖Coeff.ofFinsupp (p := r) a‖ := by
  by_cases ha : a = 0
  · simp [ha]
  have han : 0 < ‖Coeff.ofFinsupp (p := r) a‖ := by
    apply norm_pos_iff.mpr
    intro he
    apply ha
    apply Finsupp.ext
    intro n
    exact congrArg (fun x : Coeff r => x n) he
  let c : ℂ := (‖Coeff.ofFinsupp (p := r) a‖ : ℂ)⁻¹
  have hc : ‖c‖ = ‖Coeff.ofFinsupp (p := r) a‖⁻¹ := by
    simp [c, norm_inv, Complex.norm_real]
  have hnorm : ‖Coeff.ofFinsupp (p := r) (c • a)‖ ≤ 1 := by
    rw [map_smul, norm_smul, hc, inv_mul_cancel₀ han.ne']
  have he := norm_finiteHilbert_interpolate_unit h₀ h₁ hr hrtop ht₀ ht₁ hrt (c • a) hnorm
  rw [map_smul, norm_smul, hc] at he
  have ht := (mul_le_mul_of_nonneg_left he han.le)
  simpa only [← mul_assoc, mul_inv_cancel₀ han.ne', one_mul, mul_comm] using ht

/-- Every proved endpoint pair supplies its completed intermediate Hilbert estimate. -/
def HilbertEstimate.interpolate {p₀ p₁ r : ℝ≥0∞}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ r)]
    (h₀ : HilbertEstimate p₀) (h₁ : HilbertEstimate p₁)
    (hr : 1 < r) (hrtop : r ≠ ⊤) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hrt : r.toReal * ((1-t)/p₀.toReal + t/p₁.toReal) = 1) : HilbertEstimate r where
  one_lt := hr
  ne_top := hrtop
  bound := max h₀.bound h₁.bound
  bound_nonneg := h₀.bound_nonneg.trans (le_max_left _ _)
  finite_bound := norm_finiteHilbert_interpolate_le h₀ h₁ hr hrtop ht₀ ht₁ hrt

end NLS.Fourier
