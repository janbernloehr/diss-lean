import NLS.ZakharovShabat.SourceLemma6_5
import NLS.ZakharovShabat.WeightedCorrection

/-!
# The original-source inverse following Lemma 6.5

The squared Neumann construction acts on the original unweighted coefficient
pair. Its two-sided inverse agrees with the weighted inverse on every weighted
input. One locally uniform cutoff suffices on all the closed strips.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original-source squared Neumann inverse of Id−T_n. -/
def sourceComplementaryCorrection (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖(sourcePotentialInverse hp φ n z hz).comp (sourcePotentialInverse hp φ n z hz)‖ < 1) :
    CoeffPair p →L[ℂ] CoeffPair p :=
  SquaredNeumann.correction (sourcePotentialInverse hp φ n z hz) (by simpa only [pow_two, ContinuousLinearMap.mul_def] using h)

/-- The printed factorization uses the convergent even Neumann inverse. -/
theorem sourceComplementaryCorrection_formula (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖(sourcePotentialInverse hp φ n z hz).comp (sourcePotentialInverse hp φ n z hz)‖ < 1) :
    sourceComplementaryCorrection hp φ n z hz h =
      (1 + sourcePotentialInverse hp φ n z hz) *
        SquaredNeumann.evenCorrection (sourcePotentialInverse hp φ n z hz)
          (by simpa only [pow_two, ContinuousLinearMap.mul_def] using h) := rfl

/-- The even inverse is the sum of the even powers in the original operator norm. -/
theorem sourceComplementaryCorrection_even_hasSum (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖(sourcePotentialInverse hp φ n z hz).comp (sourcePotentialInverse hp φ n z hz)‖ < 1) :
    HasSum (fun j : ℕ => (sourcePotentialInverse hp φ n z hz ^ 2) ^ j)
      (SquaredNeumann.evenCorrection (sourcePotentialInverse hp φ n z hz)
        (by simpa only [pow_two, ContinuousLinearMap.mul_def] using h)) :=
  SquaredNeumann.evenCorrection_hasSum _ _

theorem sourceComplementaryCorrection_left (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖(sourcePotentialInverse hp φ n z hz).comp (sourcePotentialInverse hp φ n z hz)‖ < 1)
    (a : CoeffPair p) :
    sourceComplementaryCorrection hp φ n z hz h (a - sourcePotentialInverse hp φ n z hz a) = a :=
  SquaredNeumann.correction_left _ _ a

theorem sourceComplementaryCorrection_right (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖(sourcePotentialInverse hp φ n z hz).comp (sourcePotentialInverse hp φ n z hz)‖ < 1)
    (a : CoeffPair p) :
    sourceComplementaryCorrection hp φ n z hz h a -
      sourcePotentialInverse hp φ n z hz (sourceComplementaryCorrection hp φ n z hz h a) = a :=
  SquaredNeumann.correction_right _ _ a

/-- The original equation has a unique solution for every right-hand side. -/
theorem sourceComplementaryCorrection_unique (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖(sourcePotentialInverse hp φ n z hz).comp (sourcePotentialInverse hp φ n z hz)‖ < 1)
    (a b : CoeffPair p) (he : a - sourcePotentialInverse hp φ n z hz a = b) :
    a = sourceComplementaryCorrection hp φ n z hz h b := by
  rw [← he,sourceComplementaryCorrection_left]

/-- Weighted and original unweighted solutions coincide coefficient by coefficient. -/
theorem sourceComplementaryCorrection_weightedInput (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (h : ‖(sourcePotentialInverse hp (sourceWeightedPeriodTwoInput w φ) n z hz).comp
      (sourcePotentialInverse hp (sourceWeightedPeriodTwoInput w φ) n z hz)‖ < 1)
    (a : WeightedCoeffPair w.toWeight p) :
    sourceWeightedPeriodTwoInput w (weightedCorrection hp w φ n z hz hw a) =
      sourceComplementaryCorrection hp (sourceWeightedPeriodTwoInput w φ) n z hz h
        (sourceWeightedPeriodTwoInput w a) := by
  apply sourceComplementaryCorrection_unique
  rw [sourcePotentialInverse_weightedInput, ← map_sub, weightedCorrection_right]

/-- Locally uniform existence of compatible two-sided inverses in both original norms. -/
theorem exists_uniform_sourceComplementaryCorrection (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ∃ A : WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p,
        ∃ B : CoeffPair p →L[ℂ] CoeffPair p,
          (∀ a, A (a - weightedPotentialInverse hp w ψ n z hz a) = a) ∧
          (∀ a, A a - weightedPotentialInverse hp w ψ n z hz (A a) = a) ∧
          (∀ a, B (a - sourcePotentialInverse hp (sourceWeightedPeriodTwoInput w ψ) n z hz a) = a) ∧
          (∀ a, B a - sourcePotentialInverse hp (sourceWeightedPeriodTwoInput w ψ) n z hz (B a) = a) ∧
          (∀ a, sourceWeightedPeriodTwoInput w (A a) = B (sourceWeightedPeriodTwoInput w a)) := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,_,hsmall⟩ := sourceLemma6_5_uniform_half hp w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ n hn z hz
  obtain ⟨hw,hs⟩ := hsmall ψ hψ n hn z hz
  have hw' := hw.trans_lt (by norm_num : (1:ℝ)/2 < 1)
  have hs' := hs.trans_lt (by norm_num : (1:ℝ)/2 < 1)
  exact ⟨weightedCorrection hp w ψ n z hz hw',
    sourceComplementaryCorrection hp (sourceWeightedPeriodTwoInput w ψ) n z hz hs',
    weightedCorrection_left hp w ψ n z hz hw', weightedCorrection_right hp w ψ n z hz hw',
    sourceComplementaryCorrection_left hp _ n z hz hs', sourceComplementaryCorrection_right hp _ n z hz hs',
    sourceComplementaryCorrection_weightedInput hp w ψ n z hz hw' hs'⟩

end NLS.ZakharovShabat
