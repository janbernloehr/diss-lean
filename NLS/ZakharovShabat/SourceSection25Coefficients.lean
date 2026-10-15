import NLS.ZakharovShabat.LinearWeightCoefficientAnalytic
import NLS.ZakharovShabat.NormalizedWeightedSource

/-! # Original Section 25 resonant coefficients

The original weighted norm gives the exact quadratic threshold. The
leading coefficients are evaluated at their physical signed frequencies;
both component norms and the closed-strip boundary are retained.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The second diagonal representation in (5.7), tested on the negative mode. -/
theorem weightedResonantA_parity_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantA hp w φ n z hz h =
      resonantCoordinates w.toWeight n
        (weightedPotentialInverse hp w φ n z hz (weightedResonantEvenVector hp w φ n z hz h 0)) 0 := by
  unfold weightedResonantA
  change resonantCoordinates w.toWeight n
    (weightedCorrection hp w φ n z hz h (weightedResonantSource hp w φ n 0)) 0 = _
  rw [weightedCorrection_formula]
  change resonantCoordinates w.toWeight n (weightedResonantEvenVector hp w φ n z hz h 0 +
    weightedPotentialInverse hp w φ n z hz (weightedResonantEvenVector hp w φ n z hz h 0)) 0 = _
  rw [map_add,Pi.add_apply,resonantCoordinates_zero,weightedResonantEvenVector_zero_fst]
  simp

/-- Lemma 25.2 in the original weighted source norm, on every closed-strip point. -/
theorem sourceM1_square_bound (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : CoeffPair 2) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift (by simp) w (normalizedWeightedPeriodOne w a) n z hz‖ ≤
      (4/(1+|(n:ℝ)|))*‖a‖^2 := by
  simpa only [norm_normalizedWeightedPeriodOne] using
    norm_weightedPotentialSquareInShift_linear w hw (normalizedWeightedPeriodOne w a) n z hz

/-- Lemma 25.3: analytic coefficients and their exact componentwise bounds. -/
theorem sourceM1_coefficients (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : CoeffPair 2) (n : ℤ) (hn : 8*‖a‖^2 ≤ 1+|(n:ℝ)|) :
    let φ := normalizedWeightedPeriodOne w a
    let ψ := normalizedWeightedSource w a
    AnalyticOnNhd ℂ (weightedResonantAExtension (by simp) w φ n) (resonantStrip n) ∧
    AnalyticOnNhd ℂ (weightedResonantBPlusExtension (by simp) w φ n) (resonantStrip n) ∧
    AnalyticOnNhd ℂ (weightedResonantBMinusExtension (by simp) w φ n) (resonantStrip n) ∧
    ∀ z ∈ resonantStrip n,
      ‖weightedResonantAExtension (by simp) w φ n z‖ ≤ ‖a‖^2/(1+|(n:ℝ)|) ∧
      w (2*n)*‖weightedResonantBPlusExtension (by simp) w φ n z-ψ.snd n‖ ≤
        (8/(1+|(n:ℝ)|))*‖a‖^2*‖a.snd‖ ∧
      w (2*n)*‖weightedResonantBMinusExtension (by simp) w φ n z-ψ.fst (-n)‖ ≤
        (8/(1+|(n:ℝ)|))*‖a‖^2*‖a.fst‖ := by
  have hf : ‖(normalizedWeightedPeriodOne w a).fst‖ = ‖a.fst‖ := by
    change ‖(WeightedCoeff.weightIsometry w.toWeight 2).symm (Coeff.periodDouble a.fst)‖ = _
    rw [(WeightedCoeff.weightIsometry w.toWeight 2).symm.norm_map,Coeff.norm_periodDouble]
  have hg : ‖(normalizedWeightedPeriodOne w a).snd‖ = ‖a.snd‖ := by
    change ‖(WeightedCoeff.weightIsometry w.toWeight 2).symm (Coeff.periodDouble a.snd)‖ = _
    rw [(WeightedCoeff.weightIsometry w.toWeight 2).symm.norm_map,Coeff.norm_periodDouble]
  have h := linearWeight_resonantCoefficients w hw (normalizedWeightedPeriodOne w a) n
    (by simpa only [norm_normalizedWeightedPeriodOne] using hn)
  simpa only [norm_normalizedWeightedPeriodOne,hf,hg,normalizedWeightedSource_snd,
    normalizedWeightedSource_fst,show -(2*n) = 2*(-n) by ring,
    normalizedWeightedPeriodOne_fst_even,normalizedWeightedPeriodOne_snd_even] using h

/-- The exact quadratic threshold gives a one-half contraction, including its boundary. -/
theorem sourceM1_square_contraction (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : CoeffPair 2) (n : ℤ) (hn : 8*‖a‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift (by simp) w (normalizedWeightedPeriodOne w a) n z hz‖ ≤ (1/2:ℝ) := by
  exact norm_weightedPotentialSquareInShift_le_half w hw (normalizedWeightedPeriodOne w a) n z hz
    (by simpa only [norm_normalizedWeightedPeriodOne] using hn)

/-- The coefficients are jointly analytic in the original normalized source and spectral parameter. -/
theorem sourceM1_coefficients_joint_analytic (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : CoeffPair 2) (n : ℤ) (hn : 8*‖a‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    AnalyticAt ℂ (fun x : CoeffPair 2 × ℂ =>
      weightedResonantAExtension (by simp) w (normalizedWeightedPeriodOne w x.1) n x.2) (a,z) ∧
    AnalyticAt ℂ (fun x : CoeffPair 2 × ℂ =>
      weightedResonantBPlusExtension (by simp) w (normalizedWeightedPeriodOne w x.1) n x.2) (a,z) ∧
    AnalyticAt ℂ (fun x : CoeffPair 2 × ℂ =>
      weightedResonantBMinusExtension (by simp) w (normalizedWeightedPeriodOne w x.1) n x.2) (a,z) := by
  have hdom := mem_weightedCorrectionDomain_linear w hw (normalizedWeightedPeriodOne w a) n z hz
    (by simpa only [norm_normalizedWeightedPeriodOne] using hn)
  have hf : AnalyticAt ℂ (fun x : CoeffPair 2 × ℂ => (normalizedWeightedPeriodOne w x.1,x.2)) (a,z) :=
    (((normalizedWeightedPeriodOne w).toContinuousLinearMap.analyticAt a).comp analyticAt_fst).prod analyticAt_snd
  exact ⟨(analyticAt_weightedResonantAExtension (by simp) w n _ hdom).comp
      (x := (a,z)) (f := fun x : CoeffPair 2 × ℂ => (normalizedWeightedPeriodOne w x.1,x.2)) hf,
    (analyticAt_weightedResonantBPlusExtension (by simp) w n _ hdom).comp
      (x := (a,z)) (f := fun x : CoeffPair 2 × ℂ => (normalizedWeightedPeriodOne w x.1,x.2)) hf,
    (analyticAt_weightedResonantBMinusExtension (by simp) w n _ hdom).comp
      (x := (a,z)) (f := fun x : CoeffPair 2 × ℂ => (normalizedWeightedPeriodOne w x.1,x.2)) hf⟩

end NLS.ZakharovShabat
