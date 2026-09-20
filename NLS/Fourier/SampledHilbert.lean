import NLS.Fourier.PerturbedHilbertRows

/-!
# Uniform lp bounds for sampled off-diagonal Hilbert series

Every row may be sampled at a different complex displacement of norm at most
one half. The signed series is the ordinary bounded Hilbert transform plus
the square-kernel correction, so it retains its original lp exponent.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The ordinary reciprocal row is absolutely summable at every finite exponent above one. -/
theorem summable_norm_hilbertSeries_of_finite (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) (n : ℤ) :
    Summable (fun k : ℤ => ‖a k/((k : ℂ)-n)‖) := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  exact summable_norm_hilbertSeries (q := p.conjExponent)
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne a n

/-- The perturbed off-diagonal series is absolutely summable in every row. -/
theorem summable_norm_perturbedHilbertSeries (hp1 : 1 < p) (hp : p ≠ ⊤)
    (t : ℤ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) (n : ℤ) :
    Summable (fun k : ℤ => ‖perturbedHilbertTerm t a n k‖) :=
  ((summable_norm_perturbedHilbert_correction t ht a n).add
    (summable_norm_hilbertSeries_of_finite hp1 hp a n)).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => norm_le_norm_sub_add (perturbedHilbertTerm t a n k) (a k/((k : ℂ)-n)))

/-- The sampled signed reciprocal series as an actual lp coefficient sequence. -/
def sampledHilbert (hp1 : 1 < p) (hp : p ≠ ⊤) (t : ℤ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) : Coeff p :=
  hilbertTransform hp1 hp a+perturbedHilbertCorrection t ht a

/-- The coefficient construction agrees with the absolutely convergent perturbed series. -/
theorem sampledHilbert_apply (hp1 : 1 < p) (hp : p ≠ ⊤) (t : ℤ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) (n : ℤ) :
    sampledHilbert hp1 hp t ht a n = ∑' k : ℤ, perturbedHilbertTerm t a n k := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  change hilbertTransform hp1 hp a n+(∑' k : ℤ, (perturbedHilbertTerm t a n k-a k/((k : ℂ)-n))) = _
  rw [hilbertTransform_apply hp1 hp
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne,
    (summable_norm_perturbedHilbertSeries hp1 hp t ht a n).of_norm.tsum_sub
      (summable_norm_hilbertSeries_of_finite hp1 hp a n).of_norm]
  ring

/-- The sampled Hilbert norm bound is uniform over all half-unit complex sampling sequences. -/
theorem norm_sampledHilbert_le (hp1 : 1 < p) (hp : p ≠ ⊤) (t : ℤ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) :
    ‖sampledHilbert hp1 hp t ht a‖ ≤ (hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)*‖a‖ := by
  apply (norm_add_le _ _).trans
  have h := add_le_add (norm_hilbertTransform_apply_le hp1 hp a) (norm_perturbedHilbertCorrection_le t ht a)
  exact h.trans_eq (by ring)

/-- Signed off-diagonal reciprocal rows preserve the input lp exponent. -/
theorem memℓp_perturbedHilbertSeries (hp1 : 1 < p) (hp : p ≠ ⊤) (t : ℤ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) :
    Memℓp (fun n => ∑' k : ℤ, perturbedHilbertTerm t a n k) p := by
  have h : Memℓp (fun n => sampledHilbert hp1 hp t ht a n) p := lp.memℓp (sampledHilbert hp1 hp t ht a)
  simpa only [sampledHilbert_apply] using h

end NLS.Fourier
