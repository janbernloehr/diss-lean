import NLS.SequenceSpaces.Convolution
import NLS.SequenceSpaces.Embedding
import NLS.SequenceSpaces.Truncation

/-!
# A near/far decomposition for weighted convolution

Two conjugate-space symbols turn potential convolution into a map `lp → l1`.
Splitting each symbol into near and far frequencies isolates a potential tail
whenever the two near frequency sets have their differences outside a prescribed
finite set. This is the sequence-space decomposition used in Lemma 3.4.
-/

open scoped ENNReal
noncomputable section

namespace NLS.Coeff

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Multiplication by a conjugate-space symbol, with summable output. -/
def holderMultiplier (b : Coeff q) : Coeff p →L[ℂ] Coeff 1 :=
  (WeightedCoeff.holderProduct (p := p) (q := q)).flip b

@[simp] theorem holderMultiplier_apply (b : Coeff q) (f : Coeff p) (j : ℤ) :
    holderMultiplier b f j = f j * b j := rfl

theorem norm_holderMultiplier_apply_le (b : Coeff q) (f : Coeff p) :
    ‖holderMultiplier b f‖ ≤ ‖b‖ * ‖f‖ := by
  calc
    _ ≤ ‖WeightedCoeff.holderProduct (p := p) (q := q)‖ * ‖f‖ * ‖b‖ :=
      (WeightedCoeff.holderProduct (p := p) (q := q)).le_opNorm₂ _ _
    _ ≤ 1 * ‖f‖ * ‖b‖ := by
      gcongr
      exact WeightedCoeff.norm_holderProduct_le
    _ = _ := by ring

theorem norm_holderMultiplier_le (b : Coeff q) :
    ‖holderMultiplier (p := p) b‖ ≤ ‖b‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_holderMultiplier_apply_le b)

/-- Convolution between two conjugate-space Fourier multipliers. -/
def convolutionSandwich (a : Coeff q) (φ : Coeff p) (b : Coeff q) :
    Coeff p →L[ℂ] Coeff 1 :=
  (holderMultiplier a).comp ((convolutionCLM φ).comp (holderMultiplier b))

@[simp] theorem convolutionSandwich_apply (a : Coeff q) (φ : Coeff p) (b : Coeff q)
    (f : Coeff p) (j : ℤ) :
    convolutionSandwich a φ b f j = (∑' k : ℤ, φ (j - k) * (f k * b k)) * a j := by
  simp [convolutionSandwich, convolution_apply]

theorem norm_convolutionSandwich_apply_le (a : Coeff q) (φ : Coeff p) (b : Coeff q)
    (f : Coeff p) : ‖convolutionSandwich a φ b f‖ ≤ ‖a‖ * ‖φ‖ * ‖b‖ * ‖f‖ := by
  calc
    _ ≤ ‖a‖ * ‖convolution φ (holderMultiplier b f)‖ := norm_holderMultiplier_apply_le _ _
    _ ≤ ‖a‖ * (‖φ‖ * (‖b‖ * ‖f‖)) := by
      gcongr
      exact (norm_convolution_le _ _).trans
        (mul_le_mul_of_nonneg_left (norm_holderMultiplier_apply_le b f) (norm_nonneg _))
    _ = _ := by ring

theorem norm_convolutionSandwich_le (a : Coeff q) (φ : Coeff p) (b : Coeff q) :
    ‖convolutionSandwich a φ b‖ ≤ ‖a‖ * ‖φ‖ * ‖b‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_convolutionSandwich_apply_le a φ b)

theorem convolutionSandwich_add_left (a a' : Coeff q) (φ : Coeff p) (b : Coeff q) :
    convolutionSandwich (a + a') φ b = convolutionSandwich a φ b + convolutionSandwich a' φ b := by
  apply ContinuousLinearMap.ext
  intro f
  ext j
  simp [mul_add]

theorem convolutionSandwich_add_right (a : Coeff q) (φ : Coeff p) (b b' : Coeff q) :
    convolutionSandwich a φ (b + b') = convolutionSandwich a φ b + convolutionSandwich a φ b' := by
  have hb : holderMultiplier (p := p) (b + b') = holderMultiplier b + holderMultiplier b' := by
    apply ContinuousLinearMap.ext
    intro f
    ext j
    simp [mul_add]
  simp only [convolutionSandwich, hb, ContinuousLinearMap.comp_add]

/-- The near-near part only sees potential frequencies outside `F`. -/
theorem convolutionSandwich_truncate_eq_tail (a : Coeff q) (φ : Coeff p) (b : Coeff q)
    (A B F : Finset ℤ) (hsep : ∀ j ∈ A, ∀ k ∈ B, j - k ∉ F) :
    convolutionSandwich (truncate A a) φ (truncate B b) =
      convolutionSandwich (truncate A a) (φ - truncate F φ) (truncate B b) := by
  apply ContinuousLinearMap.ext
  intro f
  ext j
  simp only [convolutionSandwich_apply]
  by_cases hj : j ∈ A
  · congr 1
    apply tsum_congr
    intro k
    by_cases hk : k ∈ B
    · simp [hk, hsep j hj k hk]
    · simp [hk]
  · simp [hj]

/-- Decompose into far output, far input, and near-near potential-tail terms. -/
theorem convolutionSandwich_decomposition (a : Coeff q) (φ : Coeff p) (b : Coeff q)
    (A B F : Finset ℤ) (hsep : ∀ j ∈ A, ∀ k ∈ B, j - k ∉ F) :
    convolutionSandwich a φ b =
      convolutionSandwich (a - truncate A a) φ b +
      convolutionSandwich (truncate A a) φ (b - truncate B b) +
      convolutionSandwich (truncate A a) (φ - truncate F φ) (truncate B b) := by
  have ha : a = (a - truncate A a) + truncate A a := by abel
  have hb : b = (b - truncate B b) + truncate B b := by abel
  calc
    convolutionSandwich a φ b = convolutionSandwich (a - truncate A a) φ b +
        convolutionSandwich (truncate A a) φ b := by
      conv_lhs => rw [ha, convolutionSandwich_add_left]
    _ = convolutionSandwich (a - truncate A a) φ b +
        (convolutionSandwich (truncate A a) φ (b - truncate B b) +
          convolutionSandwich (truncate A a) φ (truncate B b)) := by
      conv_lhs => rhs; rw [hb, convolutionSandwich_add_right]
    _ = _ := by rw [convolutionSandwich_truncate_eq_tail a φ b A B F hsep, add_assoc]

/-- The norm estimate separates the two reciprocal-symbol tails and the potential tail. -/
theorem norm_convolutionSandwich_le_split (a : Coeff q) (φ : Coeff p) (b : Coeff q)
    (A B F : Finset ℤ) (hsep : ∀ j ∈ A, ∀ k ∈ B, j - k ∉ F) :
    ‖convolutionSandwich a φ b‖ ≤
      ‖a - truncate A a‖ * ‖φ‖ * ‖b‖ +
      ‖a‖ * ‖φ‖ * ‖b - truncate B b‖ +
      ‖a‖ * ‖φ - truncate F φ‖ * ‖b‖ := by
  rw [convolutionSandwich_decomposition a φ b A B F hsep]
  have hq : q ≠ 0 := (zero_lt_one.trans_le (show 1 ≤ q from Fact.out)).ne'
  calc
    _ ≤ ‖convolutionSandwich (a - truncate A a) φ b‖ +
        ‖convolutionSandwich (truncate A a) φ (b - truncate B b)‖ +
        ‖convolutionSandwich (truncate A a) (φ - truncate F φ) (truncate B b)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      gcongr
      · exact norm_convolutionSandwich_le _ _ _
      · exact (norm_convolutionSandwich_le _ _ _).trans (by
          gcongr
          exact norm_truncate_le hq A a)
      · exact (norm_convolutionSandwich_le _ _ _).trans (by
          gcongr
          · exact norm_truncate_le hq A a
          · exact norm_truncate_le hq B b)

/-- A common full-symbol bound and a common symbol-tail bound give the
three-term estimate in a form suitable for the double resolvent. -/
theorem norm_convolutionSandwich_le_split_of_bounds (a : Coeff q) (φ : Coeff p) (b : Coeff q)
    (A B F : Finset ℤ) (hsep : ∀ j ∈ A, ∀ k ∈ B, j - k ∉ F)
    {U V : ℝ} (ha : ‖a‖ ≤ U) (hb : ‖b‖ ≤ U)
    (haT : ‖a - truncate A a‖ ≤ V) (hbT : ‖b - truncate B b‖ ≤ V) :
    ‖convolutionSandwich a φ b‖ ≤ 2 * U * V * ‖φ‖ + U ^ 2 * ‖φ - truncate F φ‖ := by
  have hU := (norm_nonneg a).trans ha
  have hV := (norm_nonneg _).trans haT
  calc
    _ ≤ ‖a - truncate A a‖ * ‖φ‖ * ‖b‖ +
        ‖a‖ * ‖φ‖ * ‖b - truncate B b‖ +
        ‖a‖ * ‖φ - truncate F φ‖ * ‖b‖ :=
      norm_convolutionSandwich_le_split a φ b A B F hsep
    _ ≤ V * ‖φ‖ * U + U * ‖φ‖ * V + U * ‖φ - truncate F φ‖ * U := by gcongr
    _ = _ := by ring

end NLS.Coeff
