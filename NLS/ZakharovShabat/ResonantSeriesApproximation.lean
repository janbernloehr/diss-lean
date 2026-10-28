import NLS.ZakharovShabat.ResonantEvenBounds
import NLS.ZakharovShabat.ResonantAnalytic

/-! # Quantitative scalar parity series for Lemma 6.8

The actual odd diagonal and strictly positive even off-diagonal series have
geometric errors on full closed strips. The signed shift is reversed once
for the diagonal and retained after the square; the off-diagonal error keeps
its exact weight w(2n). Each term and finite sum is jointly analytic near the
closed strip, before imposing contraction.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A coefficient estimate retaining its exact signed-shift weight. -/
theorem weighted_resonantCoordinate_le_shifted (w : SpectralWeight) (n s : ℤ)
    (f : WeightedCoeffPair w.toWeight p) (i : Fin 2) :
    w (n+s) * ‖resonantCoordinates w.toWeight n f i‖ ≤ w.shiftedPairNorm s f := by
  fin_cases i
  · simp [resonantCoordinates]
    have h := WeightedCoeff.norm_apply_le w.toWeight p (w.modulation (-s) f.fst) (-(n+s))
    simp only [SpectralWeight.modulation_apply] at h
    have he : -(n+s)- -s = -n := by ring
    rw [he, w.apply_neg] at h
    exact ((by simpa only [mul_comm] using (le_div_iff₀ (w.positive (n+s))).mp h) :
      w (n+s)*‖f.fst.val (-n)‖ ≤ ‖w.modulation (-s) f.fst‖).trans
        (WithLp.norm_fst_le _ (w.pairModulation s f))
  · simp [resonantCoordinates]
    have h := WeightedCoeff.norm_apply_le w.toWeight p (w.modulation s f.snd) (n+s)
    simp only [SpectralWeight.modulation_apply,add_sub_cancel_right] at h
    exact ((by simpa only [mul_comm] using (le_div_iff₀ (w.positive (n+s))).mp h) :
      w (n+s)*‖f.snd.val n‖ ≤ ‖w.modulation s f.snd‖).trans
        (WithLp.norm_snd_le _ (w.pairModulation s f))

/-- The norm of the conjugated square acts on the exact source shifted norm. -/
theorem shiftedPairNorm_square_le_opNorm (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) :
    w.shiftedPairNorm n (weightedPotentialInverse hp w φ n z hz
      (weightedPotentialInverse hp w φ n z hz f)) ≤
      ‖weightedPotentialSquareInShift hp w φ n z hz‖ * w.shiftedPairNorm n f := by
  have h := (weightedPotentialSquareInShift hp w φ n z hz).le_opNorm (w.pairModulation n f)
  simpa only [weightedPotentialSquareInShift,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply,
    SpectralWeight.shiftedPairNorm] using h

/-- A finite scalar parity series, built from the actual complementary potential powers. -/
def weightedResonantParityPartialSum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (r m : ℕ) (i j : Fin 2) : ℂ :=
  ∑ k ∈ Finset.range m, resonantCoordinates w.toWeight n
    ((weightedPotentialInverse hp w φ n z hz ^ r)
      (((weightedPotentialInverse hp w φ n z hz ^ 2)^k) (weightedResonantSource hp w φ n j))) i

/-- Finite extraction is exactly extraction of the finite vector series. -/
theorem weightedResonantParityPartialSum_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (r m : ℕ) (i j : Fin 2) :
    weightedResonantParityPartialSum hp w φ n z hz r m i j =
      resonantCoordinates w.toWeight n ((weightedPotentialInverse hp w φ n z hz ^ r)
        (weightedResonantEvenApproximation hp w φ n z hz m j)) i := by
  simp [weightedResonantParityPartialSum,weightedResonantEvenApproximation,weightedEvenPartialSum,
    map_sum,Finset.sum_apply]

/-- Uniform geometric error for the actual odd diagonal series. -/
theorem weightedResonantA_partialSum_error (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) (m : ℕ) :
    ‖weightedResonantA hp w φ n z hz h -
      weightedResonantParityPartialSum hp w φ n z hz 1 m 1 1‖ ≤
      (2 * Coeff.complementaryConstant p hp * ‖φ‖ * ‖φ.fst‖) * (1/2 : ℝ)^m := by
  rw [weightedResonantA_parity,weightedResonantParityPartialSum_eq,pow_one]
  rw [← Pi.sub_apply,← map_sub,← map_sub]
  let f := weightedResonantEvenVector hp w φ n z hz h 1 -
    weightedResonantEvenApproximation hp w φ n z hz m 1
  have hc := weighted_resonantCoordinate_le_shifted w n (-n)
    (weightedPotentialInverse hp w φ n z hz f) 1
  simp only [add_neg_cancel] at hc
  have ht := shiftedPairNorm_weightedPotentialInverse_le hp w φ (-n) n z hz f
  rw [neg_neg] at ht
  have he := shiftedPairNorm_evenVector_one_error_le hp w φ n z hz h hh m
  calc
    _ ≤ w 0 * ‖resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz f) 1‖ :=
      le_mul_of_one_le_left (norm_nonneg _) (w.one_le 0)
    _ ≤ _ := hc
    _ ≤ _ := ht
    _ ≤ (Coeff.complementaryConstant p hp * ‖φ‖) * ((2*(1/2:ℝ)^m)*‖φ.fst‖) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg (Coeff.complementaryConstant_nonneg p hp) (norm_nonneg _))
    _ = _ := by ring

/-- Weighted geometric error for either strictly positive even coefficient series. -/
theorem weightedResonant_even_partialSum_error (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) (m : ℕ) (i j : Fin 2) :
    w (2*n) * ‖resonantCoordinates w.toWeight n
      (weightedPotentialInverse hp w φ n z hz (weightedPotentialInverse hp w φ n z hz
        (weightedResonantEvenVector hp w φ n z hz h j))) i -
      weightedResonantParityPartialSum hp w φ n z hz 2 m i j‖ ≤
      (1/2 : ℝ)^m * w.shiftedPairNorm n (weightedResonantSource hp w φ n j) := by
  rw [weightedResonantParityPartialSum_eq,pow_two,mul_apply_eq_comp]
  rw [← Pi.sub_apply,← map_sub,← map_sub,← map_sub]
  let f := weightedResonantEvenVector hp w φ n z hz h j -
    weightedResonantEvenApproximation hp w φ n z hz m j
  have he := shiftedPairNorm_evenCorrection_sub_partialSum_le_half hp w φ n z hz h hh m
    (weightedResonantSource hp w φ n j)
  calc
    _ ≤ w.shiftedPairNorm n (weightedPotentialInverse hp w φ n z hz
        (weightedPotentialInverse hp w φ n z hz f)) := by
      simpa only [two_mul] using weighted_resonantCoordinate_le_shifted w n n
        (weightedPotentialInverse hp w φ n z hz (weightedPotentialInverse hp w φ n z hz f)) i
    _ ≤ _ := shiftedPairNorm_square_le_opNorm hp w φ n z hz f
    _ ≤ (1/2 : ℝ) * w.shiftedPairNorm n f :=
      mul_le_mul_of_nonneg_right hh (norm_nonneg _)
    _ ≤ (1/2 : ℝ) * ((2*(1/2:ℝ)^m)*w.shiftedPairNorm n (weightedResonantSource hp w φ n j)) :=
      mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

theorem weightedResonantBPlus_partialSum_error (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) (m : ℕ) :
    w (2*n) * ‖(weightedResonantBPlus hp w φ n z hz h - φ.snd.val (2*n)) -
      weightedResonantParityPartialSum hp w φ n z hz 2 m 1 0‖ ≤ (1/2:ℝ)^m * ‖φ.snd‖ := by
  rw [weightedResonantBPlus_remainder]
  simpa only [shiftedPairNorm_source_zero] using
    weightedResonant_even_partialSum_error hp w φ n z hz h hh m 1 0

theorem weightedResonantBMinus_partialSum_error (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) (m : ℕ) :
    w (2*n) * ‖(weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n))) -
      weightedResonantParityPartialSum hp w φ n z hz 2 m 0 1‖ ≤ (1/2:ℝ)^m * ‖φ.fst‖ := by
  rw [weightedResonantBMinus_remainder]
  simpa only [shiftedPairNorm_source_one] using
    weightedResonant_even_partialSum_error hp w φ n z hz h hh m 0 1

/-- Total extension of an individual scalar parity term. -/
def weightedResonantParityTermFunction (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (r k : ℕ) (i j : Fin 2) (z : ℂ) : ℂ :=
  resonantCoordinates w.toWeight n ((weightedPotentialExtension hp w φ n z ^ r)
    (((weightedPotentialExtension hp w φ n z ^ 2)^k) (weightedResonantSource hp w φ n j))) i

/-- Total finite sum of the actual scalar parity terms. -/
def weightedResonantParityPartialSumFunction (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (r m : ℕ) (i j : Fin 2) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range m, weightedResonantParityTermFunction hp w φ n r k i j z

theorem weightedResonantParityPartialSumFunction_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (r m : ℕ) (i j : Fin 2)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    weightedResonantParityPartialSumFunction hp w φ n r m i j z =
      weightedResonantParityPartialSum hp w φ n z hz r m i j := by
  simp only [weightedResonantParityPartialSumFunction,weightedResonantParityTermFunction,
    weightedResonantParityPartialSum,weightedPotentialExtension_eq hp w φ n z hz]

/-- Every scalar term is jointly analytic near the entire closed strip, before contraction. -/
theorem analyticAt_weightedResonantParityTermFunction (hp : p ≠ ⊤) (w : SpectralWeight)
    (n : ℤ) (r k : ℕ) (i j : Fin 2) (s : WeightedCoeffPair w.toWeight p × ℂ)
    (hs : s.2 ∈ resonantStrip n) :
    AnalyticAt ℂ (fun t : WeightedCoeffPair w.toWeight p × ℂ =>
      weightedResonantParityTermFunction hp w t.1 n r k i j t.2) s := by
  have hT := analyticAt_weightedPotentialExtension hp w n s
    (isUnit_complementaryNormalizedPencil w.toWeight n s.2 hs)
  have hsource : AnalyticAt ℂ (fun t : WeightedCoeffPair w.toWeight p × ℂ => weightedResonantSource hp w t.1 n j) s :=
    ((ContinuousLinearMap.apply ℂ (WeightedCoeffPair w.toWeight p)
      (resonantSynthesis (p := p) w.toWeight.oneDerivative n (Pi.single j 1))).analyticAt _).comp
        (((weightedDomainPotentialCLM hp w).analyticAt s.1).comp analyticAt_fst)
  have hpower := (hT.pow r).mul ((hT.pow 2).pow k)
  have hvector := ((ContinuousLinearMap.id ℂ (WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p)).analyticAt_bilinear _).comp₂ hpower hsource
  exact ((ContinuousLinearMap.proj (R := ℂ) i).comp (resonantCoordinates w.toWeight n)).analyticAt _ |>.comp hvector

/-- Analytic finite approximants agree with the displayed source series on the full strip. -/
theorem analyticAt_weightedResonantParityPartialSumFunction (hp : p ≠ ⊤) (w : SpectralWeight)
    (n : ℤ) (r m : ℕ) (i j : Fin 2) (s : WeightedCoeffPair w.toWeight p × ℂ)
    (hs : s.2 ∈ resonantStrip n) :
    AnalyticAt ℂ (fun t : WeightedCoeffPair w.toWeight p × ℂ =>
      weightedResonantParityPartialSumFunction hp w t.1 n r m i j t.2) s := by
  exact Finset.analyticAt_fun_sum (Finset.range m)
    (fun k _ => analyticAt_weightedResonantParityTermFunction hp w n r k i j s hs)

/-- One neighborhood and one cutoff give uniform geometric scalar errors, retaining w(2n). -/
theorem exists_uniform_resonantParitySeries_rate (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ m : ℕ, ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
        ‖weightedResonantAExtension hp w ψ n z -
          weightedResonantParityPartialSumFunction hp w ψ n 1 m 1 1 z‖ ≤
            (2*Coeff.complementaryConstant p hp*(‖φ‖+1)^2)*(1/2:ℝ)^m ∧
        w (2*n) * ‖(weightedResonantBPlusExtension hp w ψ n z - ψ.snd.val (2*n)) -
          weightedResonantParityPartialSumFunction hp w ψ n 2 m 1 0 z‖ ≤ (‖φ‖+1)*(1/2:ℝ)^m ∧
        w (2*n) * ‖(weightedResonantBMinusExtension hp w ψ n z - ψ.fst.val (-(2*n))) -
          weightedResonantParityPartialSumFunction hp w ψ n 2 m 0 1 z‖ ≤ (‖φ‖+1)*(1/2:ℝ)^m := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hnorm,hsmall⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro m ψ hψ n hn z hz
  have hh := (hsmall ψ hψ n hn z hz).1
  have h : ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1 := hh.trans_lt (by norm_num)
  rw [weightedResonantAExtension_eq hp w ψ n z hz h,
    weightedResonantBPlusExtension_eq hp w ψ n z hz h,
    weightedResonantBMinusExtension_eq hp w ψ n z hz h]
  simp only [weightedResonantParityPartialSumFunction_eq hp w ψ n _ _ _ _ z hz]
  have hf := (WithLp.norm_fst_le _ ψ).trans (hnorm ψ hψ).le
  have hs := (WithLp.norm_snd_le _ ψ).trans (hnorm ψ hψ).le
  have hc0 := Coeff.complementaryConstant_nonneg p hp
  refine ⟨(weightedResonantA_partialSum_error hp w ψ n z hz h hh m).trans ?_,
    (weightedResonantBPlus_partialSum_error hp w ψ n z hz h hh m).trans ?_,
    (weightedResonantBMinus_partialSum_error hp w ψ n z hz h hh m).trans ?_⟩
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      _ = (2*Coeff.complementaryConstant p hp)*(‖ψ‖*‖ψ.fst‖) := by ring
      _ ≤ (2*Coeff.complementaryConstant p hp)*((‖φ‖+1)*(‖φ‖+1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hnorm ψ hψ).le hf (norm_nonneg _) (by positivity)) (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ (1/2:ℝ)^m*(‖φ‖+1) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := mul_comm _ _
  · calc
      _ ≤ (1/2:ℝ)^m*(‖φ‖+1) := mul_le_mul_of_nonneg_left hf (by positivity)
      _ = _ := mul_comm _ _

/-- The raw Fourier modes sum in the actual weighted scalar norm. -/
theorem weightedMode_hasSum (hp : p ≠ ⊤) (w : Weight) (f : WeightedCoeff w p) :
    HasSum (fun k : ℤ => weightedMode w k (f.val k)) f := by
  have hs := ((WeightedCoeff.weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap).hasSum
    (lp.hasSum_single hp (WeightedCoeff.weightEquiv w p f))
  have he (k : ℤ) : (WeightedCoeff.weightIsometry w p).symm
      (lp.single p k (WeightedCoeff.weightEquiv w p f k)) = weightedMode w k (f.val k) := by
    apply Subtype.ext
    funext l
    change (lp.single p k ((w k:ℂ)*f.val k) : Coeff p) l / (w l:ℂ) = _
    rw [weightedMode_apply]
    by_cases h : l = k
    · subst l; simp [lp.single_apply,w.complex_ne_zero]
    · simp [lp.single_apply,h]
  change HasSum _ ((WeightedCoeff.weightIsometry w p).symm ((WeightedCoeff.weightIsometry w p) f)) at hs
  rw [LinearIsometryEquiv.symm_apply_apply] at hs
  simpa only [ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,he] using hs

/-- Both physical component Fourier modes sum to the actual weighted pair. -/
theorem weightedSignedPairMode_hasSum (hp : p ≠ ⊤) (w : Weight) (f : WeightedCoeffPair w p) :
    HasSum (fun k : ℤ => (WeightedCoeffPair.toMax w p).symm
      (weightedMode w (-k) (f.fst.val (-k)),weightedMode w k (f.snd.val k))) f := by
  have hs₁ : HasSum (fun k : ℤ => weightedMode w (-k) (f.fst.val (-k))) f.fst :=
    (Equiv.neg ℤ).hasSum_iff.mpr (weightedMode_hasSum hp w f.fst)
  have hs := ((WeightedCoeffPair.toMax w p).symm.toContinuousLinearMap).hasSum
    (hs₁.prodMk (weightedMode_hasSum hp w f.snd))
  change HasSum _ ((WeightedCoeffPair.toMax w p).symm (WeightedCoeffPair.toMax w p f)) at hs
  simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using hs


end NLS.ZakharovShabat
