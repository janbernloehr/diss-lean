import NLS.SequenceSpaces.WeightedSandwich
import NLS.SequenceSpaces.SandwichAbsoluteSum

/-! # Absolute summation of weighted convolution sandwiches

The full product-index series converges for conjugate Banach exponents,
including the summable-input endpoint. It controls the actual shifted
weighted l1 norm and has a constant-one product norm bound.
-/

noncomputable section
open scoped ENNReal
namespace NLS.SpectralWeight
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Absolute scalar terms of the weighted shifted sandwich have a finite full product sum. -/
theorem sandwich_weighted_sum (w : SpectralWeight) (i : ℤ) (a : Coeff q)
    (φ : WeightedCoeff w.toWeight p) (b : Coeff q) (f : WeightedCoeff w.toWeight p) :
    Summable (fun jk : ℤ × ℤ => w (jk.1+i) * ‖a jk.1‖ * ‖φ.val (jk.1-jk.2)‖ *
      ‖b jk.2‖ * ‖f.val jk.2‖) ∧
    (∑' jk : ℤ × ℤ, w (jk.1+i) * ‖a jk.1‖ * ‖φ.val (jk.1-jk.2)‖ * ‖b jk.2‖ * ‖f.val jk.2‖) ≤
      ‖a‖*‖φ‖*‖b‖*w.shiftedNorm i f := by
  let φW := WeightedCoeff.weightEquiv w.toWeight p φ
  let fW := WeightedCoeff.weightEquiv (w.toWeight.shift i) p (w.toShift i f)
  have hφ (k : ℤ) : ‖φW k‖ = w k * ‖φ.val k‖ := by
    simp only [φW,WeightedCoeff.weightEquiv_apply,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (w.positive k)]
  have hf (k : ℤ) : ‖fW k‖ = w (k+i) * ‖f.val k‖ := by
    simp only [fW,WeightedCoeff.weightEquiv_apply,toShift_apply,Weight.shift_apply,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive (k+i))]
  have hdom (jk : ℤ × ℤ) :
      w (jk.1+i) * ‖a jk.1‖ * ‖φ.val (jk.1-jk.2)‖ * ‖b jk.2‖ * ‖f.val jk.2‖ ≤
        ‖a jk.1‖ * ‖φW (jk.1-jk.2)‖ * ‖b jk.2‖ * ‖fW jk.2‖ := by
    rw [hφ,hf]
    have hw : w (jk.1+i) ≤ w (jk.1-jk.2)*w (jk.2+i) := by
      simpa only [show jk.1-jk.2+(jk.2+i) = jk.1+i by omega] using
        w.add_le (jk.1-jk.2) (jk.2+i)
    nlinarith [mul_le_mul_of_nonneg_right hw
      (show 0 ≤ ‖a jk.1‖*‖φ.val (jk.1-jk.2)‖*‖b jk.2‖*‖f.val jk.2‖ by positivity)]
  have hs : Summable (fun jk : ℤ × ℤ => ‖a jk.1‖ * ‖φW (jk.1-jk.2)‖ * ‖b jk.2‖ * ‖fW jk.2‖) := by
    simpa only [mul_assoc] using Coeff.summable_sandwich_terms a φW b fW
  have ht := hs.of_nonneg_of_le (fun jk => by have hw := w.positive (jk.1+i); positivity) hdom
  refine ⟨ht,?_⟩
  apply (ht.tsum_le_tsum hdom hs).trans
  have hb := Coeff.norm_magnitude_sandwich_le a φW b fW
  rw [← Coeff.tsum_sandwich_terms] at hb
  change _ ≤ ‖a‖*‖φ‖*‖b‖*w.shiftedNorm i f at hb
  simpa only [mul_assoc] using hb


/-- The actual shifted l1 output is bounded by its complete, absolutely convergent double series. -/
theorem shiftedNorm_sandwich_le_sum (w : SpectralWeight) (i : ℤ) (a : Coeff q)
    (φ : WeightedCoeff w.toWeight p) (b : Coeff q) (f : WeightedCoeff w.toWeight p) :
    w.shiftedNorm i (w.sandwich a φ b f) ≤
      ∑' jk : ℤ × ℤ, w (jk.1+i) * ‖a jk.1‖ * ‖φ.val (jk.1-jk.2)‖ * ‖b jk.2‖ * ‖f.val jk.2‖ := by
  let g := w.sandwich a φ b f
  let U (j k : ℤ) : ℂ := (w (j+i):ℂ)*a j*φ.val (j-k)*b k*f.val k
  have hs := (sandwich_weighted_sum w i a φ b f).1
  have hu (j k : ℤ) : ‖U j k‖ =
      w (j+i)*‖a j‖*‖φ.val (j-k)‖*‖b k‖*‖f.val k‖ := by
    simp only [U,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive (j+i))]
  have hc (j : ℤ) : (w (j+i):ℂ)*g.val j = ∑' k : ℤ, U j k := by
    simp only [g,sandwich_apply]
    rw [← tsum_mul_left,← tsum_mul_left]
    apply tsum_congr
    intro k
    dsimp [U]
    ring
  have hrow (j : ℤ) : w (j+i)*‖g.val j‖ ≤
      ∑' k : ℤ, w (j+i)*‖a j‖*‖φ.val (j-k)‖*‖b k‖*‖f.val k‖ := by
    have hUs : Summable (fun k : ℤ => ‖U j k‖) := by simpa only [hu] using hs.prod_factor j
    have h := norm_tsum_le_tsum_norm hUs
    rw [← hc] at h
    simpa only [hu,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive (j+i))] using h
  have hgs : Summable (fun j : ℤ => w (j+i)*‖g.val j‖) := by
    simpa only [ENNReal.toReal_one,Real.rpow_one] using
      w.summable_shiftedNorm_terms (by simp : (1:ℝ≥0∞) ≠ ⊤) i g
  calc
    _ = ∑' j : ℤ, w (j+i)*‖g.val j‖ := by
      simpa only [ENNReal.toReal_one,Real.rpow_one] using
        w.shiftedNorm_rpow_eq_tsum (by simp : (1:ℝ≥0∞) ≠ ⊤) i g
    _ ≤ ∑' j : ℤ, ∑' k : ℤ, w (j+i)*‖a j‖*‖φ.val (j-k)‖*‖b k‖*‖f.val k‖ :=
      hgs.tsum_le_tsum hrow hs.prod
    _ = _ := hs.tsum_prod.symm

end NLS.SpectralWeight
