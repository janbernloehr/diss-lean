import NLS.ZakharovShabat.SourceResonantParity
import NLS.ZakharovShabat.UnweightedResonantDeterminant

/-!
# The original analytic resonant coefficient functions

Total coefficient functions agree with the actual source correction matrix
on its small-square domain. They are jointly analytic in potential and spectral
parameter on neighborhoods of the entire distant closed strips. Forgetting a
spectral weight preserves the functions on the common correction domain.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A total extension of an original-source correction entry. -/
def sourceCorrectionEntryFunction (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ) (i j : Fin 2) : ℂ :=
  weightedCorrectionEntryExtension hp SpectralWeight.one (unitWeightedPairEquiv φ) n z i j

/-- The original diagonal coefficient, extended as a function of λ. -/
def sourceResonantAFunction (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ) : ℂ :=
  sourceCorrectionEntryFunction hp φ n z 0 0

/-- The original positive coefficient, retaining the printed sign label. -/
def sourceResonantBPlusFunction (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ) : ℂ :=
  sourceCorrectionEntryFunction hp φ n z 1 0

/-- The original negative coefficient, retaining the printed sign label. -/
def sourceResonantBMinusFunction (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ) : ℂ :=
  sourceCorrectionEntryFunction hp φ n z 0 1

/-- The total entry recovers the actual corrected source operator coefficient. -/
theorem sourceCorrectionEntryFunction_eq (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (i j : Fin 2) :
    sourceCorrectionEntryFunction hp φ n z i j = sourceCorrectionMatrix hp φ n z hz h i j :=
  weightedCorrectionEntryExtension_eq hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h i j

/-- All three total functions agree with the named original coefficients. -/
theorem sourceResonantFunctions_eq (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    sourceResonantAFunction hp φ n z = sourceResonantA hp φ n z hz h ∧
    sourceResonantBPlusFunction hp φ n z = sourceResonantBPlus hp φ n z hz h ∧
    sourceResonantBMinusFunction hp φ n z = sourceResonantBMinus hp φ n z hz h :=
  ⟨sourceCorrectionEntryFunction_eq hp φ n z hz h 0 0,
    sourceCorrectionEntryFunction_eq hp φ n z hz h 1 0,
    sourceCorrectionEntryFunction_eq hp φ n z hz h 0 1⟩

/-- Every entry is jointly analytic in the original potential and spectral parameter. -/
theorem analyticAt_sourceCorrectionEntryFunction (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (i j : Fin 2) :
    AnalyticAt ℂ (fun s : CoeffPair p × ℂ => sourceCorrectionEntryFunction hp s.1 n s.2 i j) (φ,z) := by
  have hmap : AnalyticAt ℂ (fun s : CoeffPair p × ℂ => (unitWeightedPairEquiv s.1,s.2)) (φ,z) :=
    (((unitWeightedPairEquiv (p := p)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt φ).comp analyticAt_fst).prod analyticAt_snd
  exact (analyticAt_weightedCorrectionEntryExtension hp SpectralWeight.one n (unitWeightedPairEquiv φ,z)
    (mem_weightedCorrectionDomain hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h) i j).comp (f := fun s : CoeffPair p × ℂ => (unitWeightedPairEquiv s.1,s.2)) hmap

/-- Lemma 6.8's analytic assertion, including p=1, with actual coefficient agreement on the full strips. -/
theorem sourceLemma6_8_analytic (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ n : ℤ, N ≤ n.natAbs →
        AnalyticOnNhd ℂ (fun s : CoeffPair p × ℂ => sourceResonantAFunction hp s.1 n s.2) (U ×ˢ resonantStrip n) ∧
        AnalyticOnNhd ℂ (fun s : CoeffPair p × ℂ => sourceResonantBPlusFunction hp s.1 n s.2) (U ×ˢ resonantStrip n) ∧
        AnalyticOnNhd ℂ (fun s : CoeffPair p × ℂ => sourceResonantBMinusFunction hp s.1 n s.2) (U ×ˢ resonantStrip n) ∧
        ∀ ψ ∈ U, ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
          ∃ h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv ψ) n z hz‖ < 1,
            sourceResonantAFunction hp ψ n z = sourceResonantA hp ψ n z hz h ∧
            sourceResonantBPlusFunction hp ψ n z = sourceResonantBPlus hp ψ n z hz h ∧
            sourceResonantBMinusFunction hp ψ n z = sourceResonantBMinus hp ψ n z hz h := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hdata⟩ := sourceLemma6_6_uniform hp φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro n hn
  have ha (i j : Fin 2) : AnalyticOnNhd ℂ
      (fun s : CoeffPair p × ℂ => sourceCorrectionEntryFunction hp s.1 n s.2 i j) (U ×ˢ resonantStrip n) := by
    intro s hs
    obtain ⟨h,_⟩ := hdata s.1 hs.1 n hn s.2 hs.2
    exact analyticAt_sourceCorrectionEntryFunction hp s.1 n s.2 hs.2 h i j
  refine ⟨ha 0 0,ha 1 0,ha 0 1,?_⟩
  intro ψ hψ z hz
  obtain ⟨h,_⟩ := hdata ψ hψ n hn z hz
  exact ⟨h,sourceResonantFunctions_eq hp ψ n z hz h⟩

/-- Weighted and original analytic entries agree on the common full-strip correction domain. -/
theorem sourceCorrectionEntryFunction_weightedInput (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ < 1)
    (i j : Fin 2) :
    sourceCorrectionEntryFunction hp (sourceWeightedPeriodTwoInput w φ) n z i j =
      weightedCorrectionEntryExtension hp w φ n z i j := by
  rw [sourceCorrectionEntryFunction,unitWeightedPairEquiv_sourceWeightedInput]
  exact (weightedCorrectionEntryExtension_forget hp w φ n z hz hw h1 i j).symm

/-- One weighted neighborhood identifies all entries on every sufficiently distant closed strip. -/
theorem exists_uniform_sourceResonantFunctions_weightedInput (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
        sourceResonantAFunction hp (sourceWeightedPeriodTwoInput w ψ) n z = weightedResonantAExtension hp w ψ n z ∧
        sourceResonantBPlusFunction hp (sourceWeightedPeriodTwoInput w ψ) n z = weightedResonantBPlusExtension hp w ψ n z ∧
        sourceResonantBMinusFunction hp (sourceWeightedPeriodTwoInput w ψ) n z = weightedResonantBMinusExtension hp w ψ n z := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,_,hsmall⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ n hn z hz
  obtain ⟨hw,h1⟩ := hsmall ψ hψ n hn z hz
  rw [← sourceSquareNorm_one hp] at h1
  have hentry := sourceCorrectionEntryFunction_weightedInput hp w ψ n z hz
    (hw.trans_lt (by norm_num : (1:ℝ)/2 < 1)) (h1.trans_lt (by norm_num : (1:ℝ)/2 < 1))
  exact ⟨hentry 0 0,hentry 1 0,hentry 0 1⟩

end NLS.ZakharovShabat
