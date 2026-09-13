import NLS.ZakharovShabat.WeightedCorrectionAnalytic
import NLS.ZakharovShabat.ResonantPotentialModes
import NLS.ZakharovShabat.ResonantDiagonalSymmetry

/-!
# Analyticity of the resonant coefficients in Lemma 6.8

Continuous resonant extraction of the actual analytic correction gives total
coefficient extensions with the source's signs and basis labels. One potential
neighborhood and one cutoff give analyticity throughout all distant closed strips.
The coefficient summability estimates of Lemma 6.8 are separate results.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A total extension of one entry of the actual correction matrix in physical basis order. -/
def weightedCorrectionEntryExtension (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (i j : Fin 2) : ℂ :=
  resonantCoordinates w.toWeight n (weightedCorrectionExtension hp w φ n z (weightedResonantSource hp w φ n j)) i

/-- The total matrix-entry extension recovers the actual correction matrix. -/
theorem weightedCorrectionEntryExtension_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (i j : Fin 2) :
    weightedCorrectionEntryExtension hp w φ n z i j = weightedCorrectionMatrix hp w φ n z hz h i j := by
  rw [weightedCorrectionEntryExtension, weightedCorrectionExtension_eq hp w φ n z hz h]
  rfl

/-- Every correction entry is jointly analytic on the open correction domain. -/
theorem analyticAt_weightedCorrectionEntryExtension (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (s : WeightedCoeffPair w.toWeight p × ℂ) (hs : s ∈ weightedCorrectionDomain hp w n) (i j : Fin 2) :
    AnalyticAt ℂ (fun t : WeightedCoeffPair w.toWeight p × ℂ => weightedCorrectionEntryExtension hp w t.1 n t.2 i j) s := by
  have hsource : AnalyticAt ℂ (fun t : WeightedCoeffPair w.toWeight p × ℂ => weightedResonantSource hp w t.1 n j) s :=
    ((ContinuousLinearMap.apply ℂ (WeightedCoeffPair w.toWeight p)
      (resonantSynthesis (p := p) w.toWeight.oneDerivative n (Pi.single j 1))).analyticAt _).comp
        (((weightedDomainPotentialCLM hp w).analyticAt s.1).comp analyticAt_fst)
  have hvector := ((ContinuousLinearMap.id ℂ (WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p)).analyticAt_bilinear _).comp₂
    (analyticAt_weightedCorrectionExtension hp w n s hs) hsource
  exact ((ContinuousLinearMap.proj (R := ℂ) i).comp (resonantCoordinates w.toWeight n)).analyticAt _ |>.comp hvector

/-- Total extension of the common diagonal coefficient. -/
def weightedResonantAExtension (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) : ℂ := weightedCorrectionEntryExtension hp w φ n z 0 0

/-- Total extension of the source's positive coefficient (physical lower off-diagonal). -/
def weightedResonantBPlusExtension (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) : ℂ := weightedCorrectionEntryExtension hp w φ n z 1 0

/-- Total extension of the source's negative coefficient (physical upper off-diagonal). -/
def weightedResonantBMinusExtension (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) : ℂ := weightedCorrectionEntryExtension hp w φ n z 0 1

/-- The diagonal extension agrees with the actual source coefficient. -/
theorem weightedResonantAExtension_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantAExtension hp w φ n z = weightedResonantA hp w φ n z hz h :=
  weightedCorrectionEntryExtension_eq hp w φ n z hz h 0 0

/-- The positive off-diagonal extension preserves the source label. -/
theorem weightedResonantBPlusExtension_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantBPlusExtension hp w φ n z = weightedResonantBPlus hp w φ n z hz h :=
  weightedCorrectionEntryExtension_eq hp w φ n z hz h 1 0

/-- The negative off-diagonal extension preserves the source label. -/
theorem weightedResonantBMinusExtension_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantBMinusExtension hp w φ n z = weightedResonantBMinus hp w φ n z hz h :=
  weightedCorrectionEntryExtension_eq hp w φ n z hz h 0 1

/-- Joint analyticity of the diagonal coefficient. -/
theorem analyticAt_weightedResonantAExtension (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (s : WeightedCoeffPair w.toWeight p × ℂ) (hs : s ∈ weightedCorrectionDomain hp w n) :
    AnalyticAt ℂ (fun t : WeightedCoeffPair w.toWeight p × ℂ => weightedResonantAExtension hp w t.1 n t.2) s :=
  analyticAt_weightedCorrectionEntryExtension hp w n s hs 0 0

/-- Joint analyticity of the positive off-diagonal coefficient. -/
theorem analyticAt_weightedResonantBPlusExtension (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (s : WeightedCoeffPair w.toWeight p × ℂ) (hs : s ∈ weightedCorrectionDomain hp w n) :
    AnalyticAt ℂ (fun t : WeightedCoeffPair w.toWeight p × ℂ => weightedResonantBPlusExtension hp w t.1 n t.2) s :=
  analyticAt_weightedCorrectionEntryExtension hp w n s hs 1 0

/-- Joint analyticity of the negative off-diagonal coefficient. -/
theorem analyticAt_weightedResonantBMinusExtension (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (s : WeightedCoeffPair w.toWeight p × ℂ) (hs : s ∈ weightedCorrectionDomain hp w n) :
    AnalyticAt ℂ (fun t : WeightedCoeffPair w.toWeight p × ℂ => weightedResonantBMinusExtension hp w t.1 n t.2) s :=
  analyticAt_weightedCorrectionEntryExtension hp w n s hs 0 1

/-- One open convex potential neighborhood and cutoff put all distant closed strips in the analytic domain. -/
theorem exists_uniform_weightedCorrectionDomain (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ n : ℤ, N ≤ n.natAbs → U ×ˢ resonantStrip n ⊆ weightedCorrectionDomain hp w n := by
  obtain ⟨N, hN, U, ho, hc, hφ, h0, _, hb⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨N, hN, U, ho, hc, hφ, h0, ?_⟩
  intro n hn s hs
  exact mem_weightedCorrectionDomain hp w s.1 n s.2 hs.2 ((hb s.1 hs.1 n hn s.2 hs.2).1.trans_lt (by norm_num))

/-- The analytic assertion of Lemma 6.8, uniformly over a potential neighborhood.
The preceding agreement theorems identify these total functions with the actual source coefficients. -/
theorem exists_uniform_analyticResonantCoefficients (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ n : ℤ, N ≤ n.natAbs →
        AnalyticOnNhd ℂ (fun s : WeightedCoeffPair w.toWeight p × ℂ => weightedResonantAExtension hp w s.1 n s.2) (U ×ˢ resonantStrip n) ∧
        AnalyticOnNhd ℂ (fun s : WeightedCoeffPair w.toWeight p × ℂ => weightedResonantBPlusExtension hp w s.1 n s.2) (U ×ˢ resonantStrip n) ∧
        AnalyticOnNhd ℂ (fun s : WeightedCoeffPair w.toWeight p × ℂ => weightedResonantBMinusExtension hp w s.1 n s.2) (U ×ˢ resonantStrip n) ∧
        ∀ ψ ∈ U, ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
          ∃ h : ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1,
            weightedResonantAExtension hp w ψ n z = weightedResonantA hp w ψ n z hz h ∧
            weightedResonantBPlusExtension hp w ψ n z = weightedResonantBPlus hp w ψ n z hz h ∧
            weightedResonantBMinusExtension hp w ψ n z = weightedResonantBMinus hp w ψ n z hz h := by
  obtain ⟨N, hN, U, ho, hc, hφ, h0, _, hb⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨N, hN, U, ho, hc, hφ, h0, ?_⟩
  intro n hn
  have hsmall (ψ : WeightedCoeffPair w.toWeight p) (hψ : ψ ∈ U) (z : ℂ) (hz : z ∈ resonantStrip n) :
      ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1 := (hb ψ hψ n hn z hz).1.trans_lt (by norm_num)
  have hdom : U ×ˢ resonantStrip n ⊆ weightedCorrectionDomain hp w n :=
    fun s hs => mem_weightedCorrectionDomain hp w s.1 n s.2 hs.2 (hsmall s.1 hs.1 s.2 hs.2)
  refine ⟨fun s hs => analyticAt_weightedResonantAExtension hp w n s (hdom hs),
    fun s hs => analyticAt_weightedResonantBPlusExtension hp w n s (hdom hs),
    fun s hs => analyticAt_weightedResonantBMinusExtension hp w n s (hdom hs), ?_⟩
  intro ψ hψ z hz
  exact ⟨hsmall ψ hψ z hz, weightedResonantAExtension_eq hp w ψ n z hz _,
    weightedResonantBPlusExtension_eq hp w ψ n z hz _, weightedResonantBMinusExtension_eq hp w ψ n z hz _⟩

end NLS.ZakharovShabat
