import NLS.SequenceSpaces.SpectralConvolution
import NLS.ZakharovShabat.ComplementaryL1
import NLS.ZakharovShabat.ComplementaryShiftedNorm

/-!
# Section 6, Lemma 6.4: the potential-composed complementary inverse

`T_n = Φ A_λ⁻¹ Q_n` is a bounded operator on the source's weighted pair space.
Its uniform estimate reverses the sign of the shifted norm, exactly as in the
source. The constant depends only on the finite Banach exponent and is two in
the Hilbert case. The composition is identified with the original potential
operator acting on the previously constructed derivative-domain inverse.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Section 6 operator `T_n=Φ A_λ⁻¹ Q_n`, with the physical components exchanged by `Φ`. -/
def weightedPotentialInverse (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p :=
  (WeightedCoeffPair.mapComponents w.toWeight w.toWeight
    ((w.convolutionCLM φ.fst).comp (complementaryScalarL1 hp w.toWeight n z hz false))
    ((w.convolutionCLM φ.snd).comp (complementaryScalarL1 hp w.toWeight n z hz true))).comp
      (LinearIsometryEquiv.withLpProdComm p ℂ (WeightedCoeff w.toWeight p)
        (WeightedCoeff w.toWeight p)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem weightedPotentialInverse_fst (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    (weightedPotentialInverse hp w φ n z hz f).fst =
      w.convolution φ.fst (complementaryScalarL1 hp w.toWeight n z hz false f.snd) := rfl

@[simp] theorem weightedPotentialInverse_snd (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    (weightedPotentialInverse hp w φ n z hz f).snd =
      w.convolution φ.snd (complementaryScalarL1 hp w.toWeight n z hz true f.fst) := rfl

/-- Scalar shifted estimate for each off-diagonal product. -/
theorem shiftedNorm_potential_complementary_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ a : WeightedCoeff w.toWeight p) (i n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (b : Bool) :
    w.shiftedNorm i (w.convolution φ (complementaryScalarL1 hp w.toWeight n z hz b a)) ≤
      (Coeff.complementaryConstant p hp * ‖φ‖) * w.shiftedNorm i a := by
  calc
    _ ≤ ‖φ‖ * w.shiftedNorm i (complementaryScalarL1 hp w.toWeight n z hz b a) := w.shiftedNorm_convolution_le i _ _
    _ ≤ ‖φ‖ * (Coeff.complementaryConstant p hp * w.shiftedNorm i a) :=
      mul_le_mul_of_nonneg_left (shiftedNorm_complementaryScalarL1_le hp w i n z hz b a) (norm_nonneg _)
    _ = _ := by ring

/-- Lemma 6.4: uniform control of `T_n` from shift `-i` to shift `i`. -/
theorem shiftedPairNorm_weightedPotentialInverse_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (i n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    w.shiftedPairNorm i (weightedPotentialInverse hp w φ n z hz f) ≤
      (Coeff.complementaryConstant p hp * ‖φ‖) * w.shiftedPairNorm (-i) f := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  let C := Coeff.complementaryConstant p hp * ‖φ‖
  have hC : 0 ≤ C := mul_nonneg (Coeff.complementaryConstant_nonneg p hp) (norm_nonneg _)
  have h₁ : w.shiftedNorm (-i) (weightedPotentialInverse hp w φ n z hz f).fst ≤ C * w.shiftedNorm (-i) f.snd := by
    rw [weightedPotentialInverse_fst]
    apply (shiftedNorm_potential_complementary_le hp w φ.fst f.snd (-i) n z hz false).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le _ φ) (Coeff.complementaryConstant_nonneg p hp)) (norm_nonneg _)
  have h₂ : w.shiftedNorm i (weightedPotentialInverse hp w φ n z hz f).snd ≤ C * w.shiftedNorm i f.fst := by
    rw [weightedPotentialInverse_snd]
    apply (shiftedNorm_potential_complementary_le hp w φ.snd f.fst i n z hz true).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le _ φ) (Coeff.complementaryConstant_nonneg p hp)) (norm_nonneg _)
  have hs₁ : 0 ≤ w.shiftedNorm (-i) f.snd := norm_nonneg (w.toShift (-i) f.snd)
  have hs₂ : 0 ≤ w.shiftedNorm i f.fst := norm_nonneg (w.toShift i f.fst)
  have ho₁ : 0 ≤ w.shiftedNorm (-i) (weightedPotentialInverse hp w φ n z hz f).fst := norm_nonneg _
  have ho₂ : 0 ≤ w.shiftedNorm i (weightedPotentialInverse hp w φ n z hz f).snd := norm_nonneg _
  rw [SpectralWeight.shiftedPairNorm, WithLp.prod_norm_eq_add hp0]
  change (‖w.modulation (-i) (weightedPotentialInverse hp w φ n z hz f).fst‖ ^ p.toReal +
    ‖w.modulation i (weightedPotentialInverse hp w φ n z hz f).snd‖ ^ p.toReal) ^ (1 / p.toReal) ≤ _
  rw [SpectralWeight.norm_modulation, SpectralWeight.norm_modulation]
  calc
    _ ≤ ((C * w.shiftedNorm (-i) f.snd) ^ p.toReal + (C * w.shiftedNorm i f.fst) ^ p.toReal) ^ (1 / p.toReal) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      exact add_le_add (Real.rpow_le_rpow ho₁ h₁ hp0.le)
        (Real.rpow_le_rpow ho₂ h₂ hp0.le)
    _ = C * ((w.shiftedNorm (-i) f.snd ^ p.toReal + w.shiftedNorm i f.fst ^ p.toReal) ^ (1 / p.toReal)) := by
      rw [Real.mul_rpow hC hs₁, Real.mul_rpow hC hs₂, ← mul_add,
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hC,
        mul_one_div_cancel hp0.ne', Real.rpow_one]
    _ = _ := by
      change C * _ = C * ‖w.pairModulation (-i) f‖
      rw [WithLp.prod_norm_eq_add hp0 (w.pairModulation (-i) f)]
      change C * _ = C * (‖w.modulation (- -i) f.fst‖ ^ p.toReal + ‖w.modulation (-i) f.snd‖ ^ p.toReal) ^ (1 / p.toReal)
      rw [neg_neg, SpectralWeight.norm_modulation, SpectralWeight.norm_modulation, add_comm]

/-- The Hilbert case retains exactly the printed constant two. -/
theorem shiftedPairNorm_weightedPotentialInverse_two_le (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight 2) (i n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight 2) :
    w.shiftedPairNorm i (weightedPotentialInverse (by norm_num) w φ n z hz f) ≤
      (2 * ‖φ‖) * w.shiftedPairNorm (-i) f := by
  simpa only [Coeff.complementaryConstant_two] using shiftedPairNorm_weightedPotentialInverse_le (by norm_num) w φ i n z hz f

/-- Ordinary operator bound obtained by taking shift zero. -/
theorem norm_weightedPotentialInverse_apply_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    ‖weightedPotentialInverse hp w φ n z hz f‖ ≤ (Coeff.complementaryConstant p hp * ‖φ‖) * ‖f‖ := by
  simpa only [neg_zero, SpectralWeight.shiftedPairNorm_zero] using shiftedPairNorm_weightedPotentialInverse_le hp w φ 0 n z hz f

theorem norm_weightedPotentialInverse_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialInverse hp w φ n z hz‖ ≤ Coeff.complementaryConstant p hp * ‖φ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Coeff.complementaryConstant_nonneg p hp) (norm_nonneg _))
    (norm_weightedPotentialInverse_apply_le hp w φ n z hz)

/-- Exact agreement with the original potential applied to the actual domain inverse. -/
theorem weightedPotentialInverse_eq_original (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    weightedBaseToPair w (weightedPotentialInverse hp w φ n z hz f) =
      potentialOperator hp (weightedBaseToPair w φ)
        (weightedDomainToDomain w (complementaryFreeDomainInverse w.toWeight n z hz f)) := by
  apply Prod.ext <;> ext k
  · change _ = potentialMul hp (weightedBaseToPair w φ).1
      (weightedDomainToDomain w (complementaryFreeDomainInverse w.toWeight n z hz f)).2 k
    simp only [weightedBaseToPair_fst, weightedPotentialInverse_fst, SpectralWeight.convolution_apply,
      complementaryScalarL1_apply, freeFrequency_false, potentialMul_apply,
      weightedDomainToDomain_snd, complementaryFreeDomainInverse_snd]
  · change _ = potentialMul hp (weightedBaseToPair w φ).2
      (weightedDomainToDomain w (complementaryFreeDomainInverse w.toWeight n z hz f)).1 k
    simp only [weightedBaseToPair_snd, weightedPotentialInverse_snd, SpectralWeight.convolution_apply,
      complementaryScalarL1_apply, freeFrequency_true, potentialMul_apply,
      weightedDomainToDomain_fst, complementaryFreeDomainInverse_fst]

/-- Two applications restore the original shift, as needed for the squared contraction argument. -/
theorem shiftedPairNorm_weightedPotentialInverse_sq_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (i n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    w.shiftedPairNorm i ((weightedPotentialInverse hp w φ n z hz) ((weightedPotentialInverse hp w φ n z hz) f)) ≤
      (Coeff.complementaryConstant p hp * ‖φ‖) ^ 2 * w.shiftedPairNorm i f := by
  apply (shiftedPairNorm_weightedPotentialInverse_le hp w φ i n z hz _).trans
  have h := shiftedPairNorm_weightedPotentialInverse_le hp w φ (-i) n z hz f
  rw [neg_neg] at h
  calc
    _ ≤ (Coeff.complementaryConstant p hp * ‖φ‖) * ((Coeff.complementaryConstant p hp * ‖φ‖) * w.shiftedPairNorm i f) :=
      mul_le_mul_of_nonneg_left h (mul_nonneg (Coeff.complementaryConstant_nonneg p hp) (norm_nonneg _))
    _ = _ := by ring

end NLS.ZakharovShabat
