import NLS.ZakharovShabat.SourceResonantCoefficients
import NLS.ZakharovShabat.ResonantCoefficientSeries

/-!
# Equations (1.14)–(1.15) on the original source space

The actual original potential and complementary operator give convergent odd
and even coefficient series. The leading Fourier terms retain the physical
signs: second component at 2n and first component at -2n.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Unit-weight realization of the original complementary potential operator. -/
theorem sourcePotentialInverse_unitInput (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair SpectralWeight.one.toWeight p) :
    sourcePotentialInverse hp φ n z hz (sourceWeightedPeriodTwoInput SpectralWeight.one f) =
      sourceWeightedPeriodTwoInput SpectralWeight.one
        (weightedPotentialInverse hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz f) := by
  simpa only [sourceWeightedInput_unitWeightedPairEquiv] using
    sourcePotentialInverse_weightedInput hp SpectralWeight.one (unitWeightedPairEquiv φ) f n z hz

/-- Every power is transported as an actual original-source operator power. -/
theorem sourcePotentialInverse_pow_unitInput (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (j : ℕ)
    (f : WeightedCoeffPair SpectralWeight.one.toWeight p) :
    (sourcePotentialInverse hp φ n z hz ^ j) (sourceWeightedPeriodTwoInput SpectralWeight.one f) =
      sourceWeightedPeriodTwoInput SpectralWeight.one
        ((weightedPotentialInverse hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz ^ j) f) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ',pow_succ',mul_apply_eq_comp,mul_apply_eq_comp,
      ih,sourcePotentialInverse_unitInput]

/-- The original potential applied to one of the two resonant domain vectors. -/
def sourceResonantPotentialVector (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (i : Fin 2) : CoeffPair p :=
  sourceWeightedPeriodTwoInput SpectralWeight.one (weightedResonantSource hp SpectralWeight.one (unitWeightedPairEquiv φ) n i)

/-- The source vector is exactly Φe_n in the original differential realization. -/
theorem sourceResonantPotentialVector_eq (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (i : Fin 2) :
    sourceResonantPotentialVector hp φ n i =
      sourceOperator hp φ (sourceUnitDomainEquiv
        (resonantSynthesis SpectralWeight.one.toWeight.oneDerivative n (Pi.single i 1))) -
      sourceOperator hp 0 (sourceUnitDomainEquiv
        (resonantSynthesis SpectralWeight.one.toWeight.oneDerivative n (Pi.single i 1))) := by
  simp only [sourceResonantPotentialVector,weightedResonantSource,sourceWeightedDomainPotential_eq,
    sourceWeightedInput_unitWeightedPairEquiv,sourceUnitDomainEquiv_apply]

/-- The actual even Neumann vector, included in the original pair space. -/
def sourceResonantEvenVector (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (i : Fin 2) : CoeffPair p :=
  sourceWeightedPeriodTwoInput SpectralWeight.one
    (weightedResonantEvenVector hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h i)

/-- The even vector is the sum of the actual original even operator powers. -/
theorem sourceResonantEvenVector_hasSum (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (i : Fin 2) :
    HasSum (fun j : ℕ => ((sourcePotentialInverse hp φ n z hz ^ 2)^j)
      (sourceResonantPotentialVector hp φ n i)) (sourceResonantEvenVector hp φ n z hz h i) := by
  have hs := SquaredNeumann.evenSeries_hasSum_apply _ _
    (weightedEvenCorrection_hasSum hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h)
    (sourceWeightedPeriodTwoInput SpectralWeight.one)
    (weightedResonantSource hp SpectralWeight.one (unitWeightedPairEquiv φ) n i)
  simpa only [sourceResonantEvenVector,weightedResonantEvenVector,sourceResonantPotentialVector,
    ← pow_mul,sourcePotentialInverse_pow_unitInput] using hs

/-- Equation (1.14) with the original T_n and original component evaluation. -/
theorem sourceEquation1_14 (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    sourceResonantA hp φ n z hz h =
      (sourcePotentialInverse hp φ n z hz (sourceResonantEvenVector hp φ n z hz h 1)).snd n := by
  simpa only [sourceResonantA,sourceResonantEvenVector,sourcePotentialInverse_unitInput,
    sourceWeightedPeriodTwoInput_snd,resonantCoordinates_one] using
      weightedResonantA_parity hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h

/-- Equation (1.15) for the positive source coefficient, with leading physical frequency 2n. -/
theorem sourceEquation1_15_plus (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    sourceResonantBPlus hp φ n z hz h - φ.snd (2*n) =
      (sourcePotentialInverse hp φ n z hz (sourcePotentialInverse hp φ n z hz
        (sourceResonantEvenVector hp φ n z hz h 0))).snd n := by
  simpa only [sourceResonantBPlus,sourceResonantEvenVector,sourcePotentialInverse_unitInput,
    sourceWeightedPeriodTwoInput_snd,resonantCoordinates_one,unitWeightedPairEquiv_snd] using
      weightedResonantBPlus_remainder hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h

/-- Equation (1.15) for the negative source coefficient, with leading physical frequency -2n. -/
theorem sourceEquation1_15_minus (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    sourceResonantBMinus hp φ n z hz h - φ.fst (-(2*n)) =
      (sourcePotentialInverse hp φ n z hz (sourcePotentialInverse hp φ n z hz
        (sourceResonantEvenVector hp φ n z hz h 1))).fst (-n) := by
  simpa only [sourceResonantBMinus,sourceResonantEvenVector,sourcePotentialInverse_unitInput,
    sourceWeightedPeriodTwoInput_fst,resonantCoordinates_zero,unitWeightedPairEquiv_fst] using
      weightedResonantBMinus_remainder hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h

/-- The diagonal's odd series converges to the actual source coefficient. -/
theorem sourceResonantA_hasSum (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    HasSum (fun j : ℕ => (sourcePotentialInverse hp φ n z hz
      (((sourcePotentialInverse hp φ n z hz ^ 2)^j) (sourceResonantPotentialVector hp φ n 1))).snd n)
      (sourceResonantA hp φ n z hz h) := by
  simpa only [sourceResonantA,sourceResonantPotentialVector,← pow_mul,sourcePotentialInverse_pow_unitInput,
    sourcePotentialInverse_unitInput,sourceWeightedPeriodTwoInput_snd,resonantCoordinates_one] using
      weightedResonantA_hasSum hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h

/-- The positive Fourier remainder is the convergent strictly positive even series. -/
theorem sourceResonantBPlus_remainder_hasSum (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    HasSum (fun j : ℕ => (sourcePotentialInverse hp φ n z hz (sourcePotentialInverse hp φ n z hz
      (((sourcePotentialInverse hp φ n z hz ^ 2)^j) (sourceResonantPotentialVector hp φ n 0)))).snd n)
      (sourceResonantBPlus hp φ n z hz h - φ.snd (2*n)) := by
  simpa only [sourceResonantBPlus,sourceResonantPotentialVector,← pow_mul,sourcePotentialInverse_pow_unitInput,
    sourcePotentialInverse_unitInput,sourceWeightedPeriodTwoInput_snd,resonantCoordinates_one,
    unitWeightedPairEquiv_snd] using
      weightedResonantBPlus_remainder_hasSum hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h

/-- The negative Fourier remainder is the convergent strictly positive even series. -/
theorem sourceResonantBMinus_remainder_hasSum (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    HasSum (fun j : ℕ => (sourcePotentialInverse hp φ n z hz (sourcePotentialInverse hp φ n z hz
      (((sourcePotentialInverse hp φ n z hz ^ 2)^j) (sourceResonantPotentialVector hp φ n 1)))).fst (-n))
      (sourceResonantBMinus hp φ n z hz h - φ.fst (-(2*n))) := by
  simpa only [sourceResonantBMinus,sourceResonantPotentialVector,← pow_mul,sourcePotentialInverse_pow_unitInput,
    sourcePotentialInverse_unitInput,sourceWeightedPeriodTwoInput_fst,resonantCoordinates_zero,
    unitWeightedPairEquiv_fst] using
      weightedResonantBMinus_remainder_hasSum hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h

/-- The discarded even terms vanish before imposing a small-square hypothesis. -/
theorem sourceResonantA_even_term_zero (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (j : ℕ) :
    (((sourcePotentialInverse hp φ n z hz ^ 2)^j) (sourceResonantPotentialVector hp φ n 1)).snd n = 0 := by
  simpa only [sourceResonantPotentialVector,← pow_mul,sourcePotentialInverse_pow_unitInput,
    sourcePotentialInverse_unitInput,sourceWeightedPeriodTwoInput_snd,resonantCoordinates_one] using
      weightedResonantA_even_term_zero hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz j

/-- The discarded odd terms vanish before imposing a small-square hypothesis. -/
theorem sourceResonantBPlus_odd_term_zero (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (j : ℕ) :
    (sourcePotentialInverse hp φ n z hz (((sourcePotentialInverse hp φ n z hz ^ 2)^j) (sourceResonantPotentialVector hp φ n 0))).snd n = 0 := by
  simpa only [sourceResonantPotentialVector,← pow_mul,sourcePotentialInverse_pow_unitInput,
    sourcePotentialInverse_unitInput,sourceWeightedPeriodTwoInput_snd,resonantCoordinates_one] using
      weightedResonantBPlus_odd_term_zero hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz j

/-- The discarded odd terms vanish before imposing a small-square hypothesis. -/
theorem sourceResonantBMinus_odd_term_zero (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (j : ℕ) :
    (sourcePotentialInverse hp φ n z hz (((sourcePotentialInverse hp φ n z hz ^ 2)^j) (sourceResonantPotentialVector hp φ n 1))).fst (-n) = 0 := by
  simpa only [sourceResonantPotentialVector,← pow_mul,sourcePotentialInverse_pow_unitInput,
    sourcePotentialInverse_unitInput,sourceWeightedPeriodTwoInput_fst,resonantCoordinates_zero] using
      weightedResonantBMinus_odd_term_zero hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz j

end NLS.ZakharovShabat
