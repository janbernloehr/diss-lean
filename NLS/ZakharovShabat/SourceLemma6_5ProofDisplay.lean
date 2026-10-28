import NLS.ZakharovShabat.SourceLemma6_5

/-! # Correcting the final equality in the proof of Lemma 6.5

The actual intermediate Young majorant has the asserted upper bound for every
finite Banach exponent. The equality sign printed on p.39 is false: the
complementary inverse kills nonzero resonant inputs while the printed
right-hand side remains positive. The main Lemma 6.5 estimate remains valid.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual intermediate Young majorant in the last display of the proof of Lemma 6.5,
for every finite Banach exponent. The two scalar inputs are precisely the components of
g = A⁻¹ Q Φ A⁻¹ Q f, with their original signed shifts. -/
def sourceLemma65YoungMajorant (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair w.toWeight p) : ℝ :=
  let t := weightedPotentialInverse hp w φ n z hz f
  ‖φ‖^p.toReal * (w.shiftedNorm (-n) (complementaryScalarL1 hp w.toWeight n z hz false t.snd)^p.toReal +
    w.shiftedNorm n (complementaryScalarL1 hp w.toWeight n z hz true t.fst)^p.toReal)

/-- The right side printed after an equality sign on p.39, with its unspecified c_p. -/
def sourceLemma65PrintedProofBudget (C : ℝ) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (f : WeightedCoeffPair w.toWeight p) : ℝ :=
  2*C^(2*p.toReal)*‖φ‖^p.toReal *
    (‖φ‖/(1+|(n : ℝ)|)^(1/p.toReal : ℝ) + ‖weightedPairFourierTail w.toWeight n.natAbs φ‖/w n)^p.toReal *
    w.shiftedPairNorm n f ^ p.toReal

theorem sourceLemma65YoungMajorant_resonant (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (c : Fin 2 → ℂ) :
    sourceLemma65YoungMajorant hp w φ n z hz (resonantSynthesis w.toWeight n c) = 0 := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  simp [sourceLemma65YoungMajorant,Real.zero_rpow hp0.ne', sourceLemma6_4_resonant_zero, SpectralWeight.shiftedNorm]

/-- A nonzero resonant input makes the printed equality strict, for every positive constant,
every nonzero potential, every source weight and every point of every closed strip. -/
theorem sourceLemma65_printed_equality_strict (hp : p ≠ ⊤) (C : ℝ) (hC : 0 < C) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (hφ : φ ≠ 0) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (c : Fin 2 → ℂ) (hc : c ≠ 0) :
    sourceLemma65YoungMajorant hp w φ n z hz (resonantSynthesis w.toWeight n c) <
      sourceLemma65PrintedProofBudget C w φ n (resonantSynthesis w.toWeight n c) := by
  rw [sourceLemma65YoungMajorant_resonant]
  have hf : resonantSynthesis (p := p) w.toWeight n c ≠ 0 := by
    intro h
    apply hc
    simpa using congrArg (resonantCoordinates w.toWeight n) h
  have hnorm : 0 < w.shiftedPairNorm n (resonantSynthesis (p := p) w.toWeight n c) := by
    apply norm_pos_iff.mpr
    exact (map_ne_zero_iff (w.pairModulation n) (w.pairModulation n).injective).mpr hf
  have hφnorm := norm_pos_iff.mpr hφ
  have hw := w.positive n
  unfold sourceLemma65PrintedProofBudget
  positivity

/-- The Young majorant is bounded by the established p-power Lemma 6.5 budget.
This is a weak inequality, with the existing exponent-only constant. -/
theorem sourceLemma65YoungMajorant_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    sourceLemma65YoungMajorant hp w φ n z hz f ≤
      (weightedSquareBound hp w φ n)^p.toReal * w.shiftedPairNorm n f ^ p.toReal := by
  let D := weightedDoubleConstant (p := p) hp
  let B := ‖φ‖ * (1+|(n : ℝ)|)^(-(1/p.toReal)) +
    ‖weightedPairFourierTail w.toWeight n.natAbs φ‖/w n
  let K := D*B
  have hD : 0 ≤ D := weightedDoubleConstant_nonneg hp
  have hw := w.positive n
  have h1 : w.shiftedNorm (-n) (complementarySandwich hp w φ.snd n z hz false f.fst) ≤
      K*w.shiftedNorm (-n) f.fst := by
    have h := shiftedNorm_complementarySandwich_le_refined hp w φ.snd n z hz false f.fst
    simp only [reciprocalCenter,freeFrequency_false] at h
    apply h.trans
    dsimp [K,B,D]
    gcongr
    · exact norm_nonneg _
    · exact WithLp.norm_snd_le _ φ
    · exact WithLp.norm_snd_le _ (weightedPairFourierTail w.toWeight n.natAbs φ)
  have h2 : w.shiftedNorm n (complementarySandwich hp w φ.fst n z hz true f.snd) ≤
      K*w.shiftedNorm n f.snd := by
    have h := shiftedNorm_complementarySandwich_le_refined hp w φ.fst n z hz true f.snd
    simp only [reciprocalCenter,freeFrequency_true,neg_neg] at h
    apply h.trans
    dsimp [K,B,D]
    gcongr
    · exact norm_nonneg _
    · exact WithLp.norm_fst_le _ φ
    · exact WithLp.norm_fst_le _ (weightedPairFourierTail w.toWeight n.natAbs φ)
  have eg1 : complementaryScalarL1 hp w.toWeight n z hz false
      (weightedPotentialInverse hp w φ n z hz f).snd =
      complementarySandwich hp w φ.snd n z hz false f.fst := by
    apply Subtype.ext
    funext k
    simp [complementaryScalarL1_apply,complementarySandwich_apply,SpectralWeight.convolution_apply]
  have eg2 : complementaryScalarL1 hp w.toWeight n z hz true
      (weightedPotentialInverse hp w φ n z hz f).fst =
      complementarySandwich hp w φ.fst n z hz true f.snd := by
    apply Subtype.ext
    funext k
    simp [complementaryScalarL1_apply,complementarySandwich_apply,SpectralWeight.convolution_apply]
  have hpair : w.shiftedPairNorm n f ^ p.toReal =
      w.shiftedNorm (-n) f.fst ^ p.toReal + w.shiftedNorm n f.snd ^ p.toReal := by
    simpa using w.shiftedPairNorm_rpow hp n f
  unfold sourceLemma65YoungMajorant
  dsimp only
  rw [eg1,eg2]
  have hK : 0 ≤ K := by dsimp [K,B]; positivity
  have hF1 : 0 ≤ w.shiftedNorm (-n) f.fst := norm_nonneg _
  have hF2 : 0 ≤ w.shiftedNorm n f.snd := norm_nonneg _
  calc
    _ ≤ ‖φ‖^p.toReal*((K*w.shiftedNorm (-n) f.fst)^p.toReal+
        (K*w.shiftedNorm n f.snd)^p.toReal) := by
      gcongr <;> exact norm_nonneg _
    _ = (‖φ‖*K)^p.toReal * w.shiftedPairNorm n f ^ p.toReal := by
      rw [hpair,Real.mul_rpow hK hF1,Real.mul_rpow hK hF2,
        Real.mul_rpow (norm_nonneg φ) hK]
      ring
    _ = _ := by
      congr 2
      dsimp [K,B,D,weightedSquareBound]
      ring

/-- The scalar quantities in the Young majorant are exactly the two raw components
of the actual original-domain vector g, with no change of Fourier normalization. -/
theorem sourceLemma65YoungMajorant_domain_coefficients (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) (k : ℤ) :
    let t := weightedPotentialInverse hp w φ n z hz f
    let g := sourceWeightedDomainInput w (complementaryFreeDomainInverse w.toWeight n z hz t)
    g.fst.val k = (complementaryScalarL1 hp w.toWeight n z hz true t.fst).val k ∧
    g.snd.val k = (complementaryScalarL1 hp w.toWeight n z hz false t.snd).val k := by
  simp

/-- The same g realizes the actual differential potential in T_n squared. -/
theorem sourceLemma65YoungMajorant_domain_operator (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    let t := weightedPotentialInverse hp w φ n z hz f
    let g := sourceWeightedDomainInput w (complementaryFreeDomainInverse w.toWeight n z hz t)
    sourceWeightedPeriodTwoInput w (weightedPotentialInverse hp w φ n z hz t) =
      sourceOperator hp (sourceWeightedPeriodTwoInput w φ) g -
        sourceOperator hp 0 g :=
  sourceLemma6_4_operator hp w φ n z hz _

/-- The printed equality cannot hold for all inputs, at any finite Banach exponent. -/
theorem not_sourceLemma65_printed_proof_equality (hp : p ≠ ⊤) (C : ℝ) (hC : 0 < C) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (hφ : φ ≠ 0) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) :
    ¬ ∀ f, sourceLemma65YoungMajorant hp w φ n z hz f = sourceLemma65PrintedProofBudget C w φ n f := by
  intro h
  have hc : (fun _ : Fin 2 => (1 : ℂ)) ≠ 0 := by
    intro he
    have hh := congrFun he 0
    norm_num at hh
  exact (sourceLemma65_printed_equality_strict hp C hC w φ hφ n z hz _ hc).ne (h _)

/-- The actual square is bounded by the intermediate Young expression, so the
corrected display is a chain of two inequalities in the original shifted norm. -/
theorem sourceLemma65_square_le_young (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    w.shiftedPairNorm n (weightedPotentialInverse hp w φ n z hz
      (weightedPotentialInverse hp w φ n z hz f)) ^ p.toReal ≤
      sourceLemma65YoungMajorant hp w φ n z hz f := by
  let t := weightedPotentialInverse hp w φ n z hz f
  let gPlus := complementaryScalarL1 hp w.toWeight n z hz false t.snd
  let gMinus := complementaryScalarL1 hp w.toWeight n z hz true t.fst
  have h1 : w.shiftedNorm (-n) (weightedPotentialInverse hp w φ n z hz t).fst ≤
      ‖φ‖ * w.shiftedNorm (-n) gPlus := by
    rw [weightedPotentialInverse_fst]
    exact (w.shiftedNorm_convolution_le (-n) φ.fst gPlus).trans
      (mul_le_mul_of_nonneg_right (WithLp.norm_fst_le _ φ) (norm_nonneg _))
  have h2 : w.shiftedNorm n (weightedPotentialInverse hp w φ n z hz t).snd ≤
      ‖φ‖ * w.shiftedNorm n gMinus := by
    rw [weightedPotentialInverse_snd]
    exact (w.shiftedNorm_convolution_le n φ.snd gMinus).trans
      (mul_le_mul_of_nonneg_right (WithLp.norm_snd_le _ φ) (norm_nonneg _))
  rw [w.shiftedPairNorm_rpow hp]
  calc
    _ ≤ (‖φ‖ * w.shiftedNorm (-n) gPlus)^p.toReal + (‖φ‖ * w.shiftedNorm n gMinus)^p.toReal := by
      gcongr <;> exact norm_nonneg _
    _ = _ := by
      rw [Real.mul_rpow (norm_nonneg φ) (show 0 ≤ w.shiftedNorm (-n) gPlus from norm_nonneg _),
        Real.mul_rpow (norm_nonneg φ) (show 0 ≤ w.shiftedNorm n gMinus from norm_nonneg _)]
      dsimp [sourceLemma65YoungMajorant,t,gPlus,gMinus]
      ring

end NLS.ZakharovShabat
