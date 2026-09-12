import NLS.ZakharovShabat.ComplementaryFreeInverse
import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.HolderEmbedding

/-!
# Weighted `ℓ¹` gain of the complementary inverse

Hölder multiplication by the nonresonant reciprocal gives a constant depending
only on the input exponent. Arbitrary positive weights cancel exactly. The
same bound holds in each shifted scalar norm, with no shift-dependent loss.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The sign convention as an actual equivalence of physical frequency indices. -/
def freeFrequencyEquiv (b : Bool) : ℤ ≃ ℤ where
  toFun := freeFrequency b
  invFun := freeFrequency b
  left_inv k := by cases b <;> simp
  right_inv k := by cases b <;> simp

@[simp] theorem freeFrequencyEquiv_apply (b : Bool) (k : ℤ) :
    freeFrequencyEquiv b k = freeFrequency b k := rfl

theorem norm_complementarySymbol_le_lattice {q : ℝ≥0∞} (hq : 1 < q)
    {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) (m : ℤ) :
    ‖complementarySymbol n z m‖ ≤ ‖Coeff.puncturedLattice q hq (m - n)‖ := by
  by_cases hm : m = n
  · simp [hm]
  · simp only [complementarySymbol, if_neg hm, Coeff.puncturedLattice_apply,
      if_neg (sub_ne_zero.mpr hm), norm_inv, Complex.norm_intCast]
    apply inv_anti₀ _ (resonantStrip_denominator_lower hz hm)
    exact abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hm)

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

theorem memlp_complementaryReciprocal (hq : 1 < q) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (b : Bool) :
    Memℓp (fun k : ℤ => complementarySymbol n z (freeFrequency b k)) q := by
  have h := lp.memℓp (Coeff.reindex ((freeFrequencyEquiv b).trans (Equiv.subRight n)) (Coeff.puncturedLattice q hq))
  apply h.mono'
  intro k
  change ‖complementarySymbol n z (freeFrequency b k)‖ ≤ ‖Coeff.puncturedLattice q hq (freeFrequency b k - n)‖
  exact norm_complementarySymbol_le_lattice hq hz (freeFrequency b k)

/-- The actual complementary symbol in any reciprocal summability exponent `q>1`. -/
def complementaryReciprocal (hq : 1 < q) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (b : Bool) : Coeff q :=
  ⟨fun k => complementarySymbol n z (freeFrequency b k), memlp_complementaryReciprocal hq n z hz b⟩

@[simp] theorem complementaryReciprocal_apply (hq : 1 < q) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (b : Bool) (k : ℤ) :
    complementaryReciprocal hq n z hz b k = complementarySymbol n z (freeFrequency b k) := rfl

/-- The reciprocal norm is independent of its center, sign, and parameter in the strip. -/
theorem norm_complementaryReciprocal_le (hq : 1 < q) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (b : Bool) :
    ‖complementaryReciprocal hq n z hz b‖ ≤ ‖Coeff.puncturedLattice q hq‖ := by
  rw [← Coeff.norm_reindex ((freeFrequencyEquiv b).trans (Equiv.subRight n)) (Coeff.puncturedLattice q hq)]
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne'
  intro k
  simpa only [complementaryReciprocal_apply, Coeff.reindex_apply, Equiv.trans_apply,
    Equiv.subRight_apply, freeFrequencyEquiv_apply] using norm_complementarySymbol_le_lattice hq hz (freeFrequency b k)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complementary scalar inverse with output in the same weight at exponent one. -/
def complementaryScalarL1 (hp : p ≠ ⊤) (w : Weight) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (b : Bool) : WeightedCoeff w p →L[ℂ] WeightedCoeff w 1 := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  exact (WeightedCoeff.weightIsometry w 1).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((Coeff.holderProduct (q := 1)).flip (complementaryReciprocal hq n z hz b)).comp
      (WeightedCoeff.weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem complementaryScalarL1_apply (hp : p ≠ ⊤) (w : Weight) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (b : Bool) (a : WeightedCoeff w p) (k : ℤ) :
    (complementaryScalarL1 hp w n z hz b a).val k = complementarySymbol n z (freeFrequency b k) * a.val k := by
  change ((w k : ℂ) * a.val k * complementarySymbol n z (freeFrequency b k)) / (w k : ℂ) = _
  field_simp [w.complex_ne_zero k]

/-- Uniform weighted Hölder estimate, including the input endpoint `p=1`. -/
theorem norm_complementaryScalarL1_le (hp : p ≠ ⊤) (w : Weight) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (b : Bool) (a : WeightedCoeff w p) :
    ‖complementaryScalarL1 hp w n z hz b a‖ ≤ Coeff.complementaryConstant p hp * ‖a‖ := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  change ‖(WeightedCoeff.weightIsometry w 1).symm
    (Coeff.holderProduct (q := 1) (WeightedCoeff.weightIsometry w p a) (complementaryReciprocal hq n z hz b))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖WeightedCoeff.weightIsometry w p a‖ * ‖complementaryReciprocal hq n z hz b‖ := Coeff.norm_holderProduct_le _ _
    _ ≤ ‖a‖ * Coeff.complementaryConstant p hp := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_left
        ((norm_complementaryReciprocal_le hq n z hz b).trans (Coeff.norm_puncturedLattice_le_complementaryConstant p hp)) (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- Changing the weight by a shift preserves the actual reciprocal output coefficients. -/
theorem toShift_complementaryScalarL1 (hp : p ≠ ⊤) (w : SpectralWeight) (i n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (b : Bool) (a : WeightedCoeff w.toWeight p) :
    w.toShift i (complementaryScalarL1 hp w.toWeight n z hz b a) =
      complementaryScalarL1 hp (w.toWeight.shift i) n z hz b (w.toShift i a) := by
  apply Subtype.ext
  funext k
  simp only [SpectralWeight.toShift_apply, complementaryScalarL1_apply]

/-- The constant is uniform in the shifted norm as well as in the entire strip. -/
theorem shiftedNorm_complementaryScalarL1_le (hp : p ≠ ⊤) (w : SpectralWeight) (i n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (b : Bool) (a : WeightedCoeff w.toWeight p) :
    w.shiftedNorm i (complementaryScalarL1 hp w.toWeight n z hz b a) ≤
      Coeff.complementaryConstant p hp * w.shiftedNorm i a := by
  rw [SpectralWeight.shiftedNorm, toShift_complementaryScalarL1]
  exact norm_complementaryScalarL1_le hp _ n z hz b (w.toShift i a)

end NLS.ZakharovShabat
