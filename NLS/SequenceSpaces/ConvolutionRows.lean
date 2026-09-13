import NLS.SequenceSpaces.PowerYoung
import NLS.SequenceSpaces.Multiplier
import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.PeriodDoubling

/-!
# Sequence norms of convolution rows

Powered Young bounds the sequence of row norms. Contractive exponent
inclusion permits a larger inner exponent, covering both sides of the
Hilbert exponent in the diagonal estimate of Lemma 6.8.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p r q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] [Fact (1 ≤ q)]

/-- The row of products contributing to a scalar convolution at frequency `m`. -/
def convolutionRow (a : Coeff p) (b : Coeff r) (m : ℤ) : Coeff r :=
  multiplier (reindex (Equiv.subLeft m) (exponentInclusion le_top a)) b

omit [Fact (1 ≤ r)] in
@[simp] theorem convolutionRow_apply (a : Coeff p) (b : Coeff r) (m k : ℤ) :
    convolutionRow a b m k = a (m-k) * b k := rfl

/-- Increasing the inner row exponent is contractive and preserves the actual coefficients. -/
theorem norm_convolutionRow_exponent_le (hrq : r ≤ q) (a : Coeff p) (b : Coeff r) (m : ℤ) :
    ‖convolutionRow a (exponentInclusion hrq b) m‖ ≤ ‖convolutionRow a b m‖ := by
  have he : convolutionRow a (exponentInclusion hrq b) m = exponentInclusion hrq (convolutionRow a b m) := by
    ext k
    rfl
  rw [he]
  exact norm_exponentInclusion_le hrq _

/-- Powered Young constructs the actual sequence of inner row norms at the outer exponent. -/
theorem exists_convolutionRowNorm (hp : p ≠ ⊤) (hrp : r ≤ p) (a : Coeff p) (b : Coeff r) :
    ∃ d : Coeff p, (∀ m : ℤ, d m = (‖convolutionRow a b m‖ : ℝ)) ∧ ‖d‖ ≤ ‖a‖ * ‖b‖ := by
  have hr : r ≠ ⊤ := ne_top_of_le_ne_top hp hrp
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hr0 : 0 < r.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ r)).ne' hr
  have hY : PowerYoungRelation p.toReal r.toReal p.toReal r.toReal :=
    ⟨hr0, (ENNReal.toReal_le_toReal hr hp).mpr hrp, le_rfl,
      (ENNReal.toReal_le_toReal hr hp).mpr hrp, add_comm _ _⟩
  have hx := @exists_powerConvolution p.toReal r.toReal p.toReal r.toReal hY
  rw [ENNReal.ofReal_toReal hp, ENNReal.ofReal_toReal hr] at hx
  obtain ⟨d, hd, hn⟩ := hx a b
  refine ⟨d, ?_, hn⟩
  intro m
  simpa only [lp.norm_eq_tsum_rpow hr0, convolutionRow_apply] using hd m

/-- The norms of a sparser row family retain the same outer bound. -/
theorem exists_evenConvolutionRowNorm (hp : p ≠ ⊤) (hrp : r ≤ p) (a : Coeff p) (b : Coeff r) :
    ∃ d : Coeff p, (∀ n : ℤ, d n = (‖convolutionRow a b (2*n)‖ : ℝ)) ∧ ‖d‖ ≤ ‖a‖ * ‖b‖ := by
  obtain ⟨d, hd, hn⟩ := exists_convolutionRowNorm hp hrp a b
  exact ⟨periodHalve d, fun n => hd (2*n), (norm_periodHalve_le d).trans hn⟩

end NLS.Coeff
