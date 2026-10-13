import NLS.ZakharovShabat.SourcePQSplitting

/-!
# Lemma 6.4 in the original weighted source norms

The actual composition Φ A_λ⁻¹ Q_n obeys the printed opposite-shift estimate
for every finite Banach exponent, including one. The Hilbert constant is two;
at the endpoint one the elementary reciprocal bound even gives constant one.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source's exact signed shifted norm uses first physical frequency -k and second frequency k. -/
theorem sourceShiftedNorm_formula (hp : p ≠ ⊤) (w : SpectralWeight)
    (i : ℤ) (f : WeightedCoeffPair w.toWeight p) :
    w.shiftedPairNorm i f ^ p.toReal = ∑' k : ℤ, (w (k+i))^p.toReal *
      (‖f.fst.val (-k)‖^p.toReal+‖f.snd.val k‖^p.toReal) :=
  w.shiftedPairNorm_rpow_eq_tsum hp i f

/-- T_n is the potential part of the actual original operator applied to the actual complementary domain inverse. -/
theorem sourceLemma6_4_operator (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    sourceWeightedPeriodTwoInput w (weightedPotentialInverse hp w φ n z hz f) =
      sourceOperator hp (sourceWeightedPeriodTwoInput w φ)
        (sourceWeightedDomainInput w (complementaryFreeDomainInverse w.toWeight n z hz f)) -
      sourceOperator hp 0
        (sourceWeightedDomainInput w (complementaryFreeDomainInverse w.toWeight n z hz f)) := by
  rw [← weightedDomainPotential_complementaryInverse,sourceWeightedDomainPotential_eq]

/-- The actual composed potential inverse annihilates the two resonant modes. -/
theorem sourceLemma6_4_resonant_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (c : Fin 2 → ℂ) :
    weightedPotentialInverse hp w φ n z hz (resonantSynthesis w.toWeight n c) = 0 := by
  rw [← weightedDomainPotential_complementaryInverse,sourceComplementaryFreeInverse_resonant,map_zero]

/-- Lemma 6.4 with the exact original weighted norm and opposite shift, uniformly in n, i, and λ∈U_n. -/
theorem sourceLemma6_4 (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (i n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    w.shiftedPairNorm i (weightedPotentialInverse hp w φ n z hz f) ≤
      (Coeff.complementaryConstant p hp * ‖φ‖) * w.shiftedPairNorm (-i) f :=
  shiftedPairNorm_weightedPotentialInverse_le hp w φ i n z hz f

/-- The unchanged printed Hilbert constant is exactly two. -/
theorem sourceLemma6_4_two (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 2)
    (i n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair w.toWeight 2) :
    w.shiftedPairNorm i (weightedPotentialInverse (by norm_num) w φ n z hz f) ≤
      (2*‖φ‖) * w.shiftedPairNorm (-i) f :=
  shiftedPairNorm_weightedPotentialInverse_two_le w φ i n z hz f

/-- At exponent one the signed pair norm is precisely the sum of the two scalar shifted norms. -/
theorem sourceShiftedPairNorm_one (w : SpectralWeight) (i : ℤ) (f : WeightedCoeffPair w.toWeight 1) :
    w.shiftedPairNorm i f = w.shiftedNorm (-i) f.fst + w.shiftedNorm i f.snd := by
  simpa only [ENNReal.toReal_one,Real.rpow_one] using w.shiftedPairNorm_rpow (by norm_num) i f

/-- The endpoint complementary inverse is a contraction in every scalar shifted norm. -/
theorem sourceComplementaryScalarL1_one_le (w : SpectralWeight) (i n : ℤ)
    (z : ℂ) (hz : z ∈ resonantStrip n) (b : Bool) (a : WeightedCoeff w.toWeight 1) :
    w.shiftedNorm i (complementaryScalarL1 (by norm_num) w.toWeight n z hz b a) ≤ w.shiftedNorm i a := by
  apply w.shiftedNorm_mono i
  intro k
  rw [complementaryScalarL1_apply,norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (norm_complementarySymbol_le hz (freeFrequency b k)) (norm_nonneg (a.val k))

/-- The included endpoint p=1 admits constant one in the same original signed norms. -/
theorem sourceLemma6_4_one (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 1)
    (i n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair w.toWeight 1) :
    w.shiftedPairNorm i (weightedPotentialInverse (by norm_num) w φ n z hz f) ≤
      ‖φ‖ * w.shiftedPairNorm (-i) f := by
  have bound (a b : WeightedCoeff w.toWeight 1) (j : ℤ) (sgn : Bool) :
      w.shiftedNorm j (w.convolution a (complementaryScalarL1 (by norm_num) w.toWeight n z hz sgn b)) ≤
        ‖a‖*w.shiftedNorm j b :=
    (w.shiftedNorm_convolution_le j _ _).trans
      (mul_le_mul_of_nonneg_left (sourceComplementaryScalarL1_one_le w j n z hz sgn b) (norm_nonneg a))
  rw [sourceShiftedPairNorm_one,weightedPotentialInverse_fst,weightedPotentialInverse_snd]
  calc
    _ ≤ ‖φ.fst‖*w.shiftedNorm (-i) f.snd + ‖φ.snd‖*w.shiftedNorm i f.fst :=
      add_le_add (bound _ _ _ false) (bound _ _ _ true)
    _ ≤ ‖φ‖*w.shiftedNorm (-i) f.snd + ‖φ‖*w.shiftedNorm i f.fst :=
      add_le_add (mul_le_mul_of_nonneg_right (WithLp.norm_fst_le _ φ) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (WithLp.norm_snd_le _ φ) (norm_nonneg _))
    _ = _ := by rw [sourceShiftedPairNorm_one,neg_neg]; ring

end NLS.ZakharovShabat
