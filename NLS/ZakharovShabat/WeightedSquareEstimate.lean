import NLS.ZakharovShabat.ComplementaryDoubleEstimate

/-!
# Section 6, Lemma 6.5: high-frequency decay of the weighted square

The scalar double-inverse estimate yields the displayed two-component bound
for `T_n²`, in shift `n`. The estimate retains the exact weighted potential tail
and its additional factor `1/w(n)`. It is also stated as the operator norm of
the square conjugated by the shift equivalence.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The first component of the actual square factors through the opposite double inverse. -/
theorem weightedPotentialInverse_sq_fst (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    (weightedPotentialInverse hp w φ n z hz (weightedPotentialInverse hp w φ n z hz f)).fst =
      w.convolution φ.fst (complementarySandwich hp w φ.snd n z hz false f.fst) := by
  rw [weightedPotentialInverse_fst, weightedPotentialInverse_snd]
  apply congrArg (w.convolution φ.fst)
  apply Subtype.ext
  funext j
  simp only [complementaryScalarL1_apply, complementarySandwich_apply, SpectralWeight.convolution_apply,
    Bool.not_false, freeFrequency_false, freeFrequency_true]

/-- The second component has the reflected physical orientation. -/
theorem weightedPotentialInverse_sq_snd (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    (weightedPotentialInverse hp w φ n z hz (weightedPotentialInverse hp w φ n z hz f)).snd =
      w.convolution φ.snd (complementarySandwich hp w φ.fst n z hz true f.snd) := by
  rw [weightedPotentialInverse_snd, weightedPotentialInverse_fst]
  apply congrArg (w.convolution φ.snd)
  apply Subtype.ext
  funext j
  simp only [complementaryScalarL1_apply, complementarySandwich_apply, SpectralWeight.convolution_apply,
    Bool.not_true, freeFrequency_false, freeFrequency_true]

/-- The explicit Lemma 6.5 bound, written with a negative power of the inhomogeneous bracket. -/
def weightedSquareBound (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : ℝ :=
  weightedDoubleConstant (p := p) hp * ‖φ‖ *
    (‖φ‖ * (1 + |(n : ℝ)|) ^ (-(1 / p.toReal)) + ‖weightedPairFourierTail w.toWeight n.natAbs φ‖ / w n)

theorem weightedSquareBound_nonneg (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) :
    0 ≤ weightedSquareBound hp w φ n := by
  have hD := weightedDoubleConstant_nonneg (p := p) hp
  have hw := w.positive n
  unfold weightedSquareBound
  positivity

/-- Lemma 6.5 for all finite Banach exponents and every point of the full closed strip. -/
theorem shiftedPairNorm_weightedPotentialInverse_sq_refined (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    w.shiftedPairNorm n (weightedPotentialInverse hp w φ n z hz (weightedPotentialInverse hp w φ n z hz f)) ≤
      weightedSquareBound hp w φ n * w.shiftedPairNorm n f := by
  let T := weightedPotentialInverse hp w φ n z hz
  let C := weightedSquareBound hp w φ n
  have hC : 0 ≤ C := weightedSquareBound_nonneg hp w φ n
  have hD := weightedDoubleConstant_nonneg (p := p) hp
  have hw := w.positive n
  have hφ₁ : ‖φ.fst‖ ≤ ‖φ‖ := WithLp.norm_fst_le _ φ
  have hφ₂ : ‖φ.snd‖ ≤ ‖φ‖ := WithLp.norm_snd_le _ φ
  have htail₁ : ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ.fst‖ ≤ ‖weightedPairFourierTail w.toWeight n.natAbs φ‖ :=
    WithLp.norm_fst_le _ (weightedPairFourierTail w.toWeight n.natAbs φ)
  have htail₂ : ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ.snd‖ ≤ ‖weightedPairFourierTail w.toWeight n.natAbs φ‖ :=
    WithLp.norm_snd_le _ (weightedPairFourierTail w.toWeight n.natAbs φ)
  have h₁ : w.shiftedNorm (-n) (T (T f)).fst ≤ C * w.shiftedNorm (-n) f.fst := by
    rw [weightedPotentialInverse_sq_fst]
    have hinner := shiftedNorm_complementarySandwich_le_refined hp w φ.snd n z hz false f.fst
    simp only [reciprocalCenter, freeFrequency_false] at hinner
    have hf0 : 0 ≤ w.shiftedNorm (-n) f.fst := norm_nonneg _
    calc
      _ ≤ ‖φ.fst‖ * w.shiftedNorm (-n) (complementarySandwich hp w φ.snd n z hz false f.fst) := w.shiftedNorm_convolution_le _ _ _
      _ ≤ ‖φ.fst‖ * ((weightedDoubleConstant (p := p) hp *
          (‖φ.snd‖ * (1 + |(n : ℝ)|) ^ (-(1/p.toReal)) + ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ.snd‖ / w n)) *
          w.shiftedNorm (-n) f.fst) := mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
      _ ≤ ‖φ‖ * ((weightedDoubleConstant (p := p) hp *
          (‖φ‖ * (1 + |(n : ℝ)|) ^ (-(1/p.toReal)) + ‖weightedPairFourierTail w.toWeight n.natAbs φ‖ / w n)) *
          w.shiftedNorm (-n) f.fst) := by gcongr
      _ = _ := by dsimp [C, weightedSquareBound]; ring
  have h₂ : w.shiftedNorm n (T (T f)).snd ≤ C * w.shiftedNorm n f.snd := by
    rw [weightedPotentialInverse_sq_snd]
    have hinner := shiftedNorm_complementarySandwich_le_refined hp w φ.fst n z hz true f.snd
    simp only [reciprocalCenter, freeFrequency_true, neg_neg] at hinner
    have hf0 : 0 ≤ w.shiftedNorm n f.snd := norm_nonneg _
    calc
      _ ≤ ‖φ.snd‖ * w.shiftedNorm n (complementarySandwich hp w φ.fst n z hz true f.snd) := w.shiftedNorm_convolution_le _ _ _
      _ ≤ ‖φ.snd‖ * ((weightedDoubleConstant (p := p) hp *
          (‖φ.fst‖ * (1 + |(n : ℝ)|) ^ (-(1/p.toReal)) + ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ.fst‖ / w n)) *
          w.shiftedNorm n f.snd) := mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
      _ ≤ ‖φ‖ * ((weightedDoubleConstant (p := p) hp *
          (‖φ‖ * (1 + |(n : ℝ)|) ^ (-(1/p.toReal)) + ‖weightedPairFourierTail w.toWeight n.natAbs φ‖ / w n)) *
          w.shiftedNorm n f.snd) := by gcongr
      _ = _ := by dsimp [C, weightedSquareBound]; ring
  change ‖w.pairModulation n (T (T f))‖ ≤ C * ‖w.pairModulation n f‖
  calc
    _ ≤ ‖(C : ℂ) • w.pairModulation n f‖ := by
      apply WeightedCoeffPair.norm_mono hp
      · change ‖w.modulation (-n) (T (T f)).fst‖ ≤ ‖(C : ℂ) • w.modulation (-n) f.fst‖
        simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC, SpectralWeight.norm_modulation] using h₁
      · change ‖w.modulation n (T (T f)).snd‖ ≤ ‖(C : ℂ) • w.modulation n f.snd‖
        simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC, SpectralWeight.norm_modulation] using h₂
    _ = _ := by simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

/-- The square represented on the original Banach space after conjugation by the source shift. -/
def weightedPotentialSquareInShift (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p :=
  let T := weightedPotentialInverse hp w φ n z hz
  (w.pairModulation n).toContinuousLinearMap.comp ((T.comp T).comp (w.pairModulation n).symm.toContinuousLinearMap)

/-- Lemma 6.5 as the operator norm induced by the `n`-shifted pair norm. -/
theorem norm_weightedPotentialSquareInShift_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ weightedSquareBound hp w φ n := by
  apply ContinuousLinearMap.opNorm_le_bound _ (weightedSquareBound_nonneg hp w φ n)
  intro f
  have h := shiftedPairNorm_weightedPotentialInverse_sq_refined hp w φ n z hz ((w.pairModulation n).symm f)
  change ‖weightedPotentialSquareInShift hp w φ n z hz f‖ ≤ _ at h
  simpa only [SpectralWeight.shiftedPairNorm, ContinuousLinearEquiv.apply_symm_apply] using h

/-- The refined bound in the source's quotient notation. -/
theorem weightedSquareBound_eq_source (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) :
    weightedSquareBound hp w φ n = weightedDoubleConstant (p := p) hp * ‖φ‖ *
      (‖φ‖ / (1 + |(n : ℝ)|) ^ (1 / p.toReal) + ‖weightedPairFourierTail w.toWeight n.natAbs φ‖ / w n) := by
  simp only [weightedSquareBound, Real.rpow_neg (by positivity : 0 ≤ 1 + |(n : ℝ)|), div_eq_mul_inv]

/-- The displayed Lemma 6.5 inequality for the induced shifted operator norm. -/
theorem norm_weightedPotentialSquareInShift_le_source (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ weightedDoubleConstant (p := p) hp * ‖φ‖ *
      (‖φ‖ / (1 + |(n : ℝ)|) ^ (1 / p.toReal) + ‖weightedPairFourierTail w.toWeight n.natAbs φ‖ / w n) := by
  rw [← weightedSquareBound_eq_source]
  exact norm_weightedPotentialSquareInShift_le hp w φ n z hz

end NLS.ZakharovShabat
