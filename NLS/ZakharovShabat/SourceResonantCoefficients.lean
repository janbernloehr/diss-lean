import NLS.ZakharovShabat.SourceLemma6_6
import NLS.ZakharovShabat.ResonantDiagonalSymmetry

/-!
# The original resonant coefficients in both basis orders

The coefficient matrix is the actual corrected source potential evaluated on
the two resonant domain vectors. The printed order (plus, minus) reverses the
library's physical order (minus, plus); the determinant is unchanged.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual corrected potential matrix in physical order (minus, plus). -/
def sourceCorrectionMatrix (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  weightedCorrectionMatrix hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h

/-- Each matrix entry is an actual original-source corrected potential coefficient. -/
theorem sourceCorrectionMatrix_entry (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (hs : ‖(sourcePotentialInverse hp φ n z hz).comp (sourcePotentialInverse hp φ n z hz)‖ < 1)
    (i j : Fin 2) :
    sourceCorrectionMatrix hp φ n z hz h i j =
      resonantCoordinates SpectralWeight.one.toWeight n (unitWeightedPairEquiv
        (sourceComplementaryCorrection hp φ n z hz hs
          (sourceOperator hp φ (sourceUnitDomainEquiv
              (resonantSynthesis SpectralWeight.one.toWeight.oneDerivative n (Pi.single j 1))) -
            sourceOperator hp 0 (sourceUnitDomainEquiv
              (resonantSynthesis SpectralWeight.one.toWeight.oneDerivative n (Pi.single j 1)))))) i := by
  let u := resonantSynthesis (p := p) SpectralWeight.one.toWeight.oneDerivative n (Pi.single j 1)
  have hs' : ‖(sourcePotentialInverse hp
      (sourceWeightedPeriodTwoInput SpectralWeight.one (unitWeightedPairEquiv φ)) n z hz).comp
      (sourcePotentialInverse hp
        (sourceWeightedPeriodTwoInput SpectralWeight.one (unitWeightedPairEquiv φ)) n z hz)‖ < 1 := by
    simpa only [sourceWeightedInput_unitWeightedPairEquiv] using hs
  have he := sourceComplementaryCorrection_weightedInput hp SpectralWeight.one (unitWeightedPairEquiv φ)
    n z hz h hs' (weightedDomainPotential hp SpectralWeight.one (unitWeightedPairEquiv φ) u)
  rw [sourceWeightedDomainPotential_eq] at he
  simp only [sourceWeightedInput_unitWeightedPairEquiv] at he
  have hcoeff := congrArg (fun a => resonantCoordinates SpectralWeight.one.toWeight n
    (unitWeightedPairEquiv a) i) he
  rw [unitWeightedPairEquiv_sourceWeightedInput] at hcoeff
  have hf (a : WeightedCoeffPair SpectralWeight.one.toWeight p) : SpectralWeight.one.forgetPairWeight a = a := by
    apply weightedPair_ext <;> intro k <;> simp
  rw [hf] at hcoeff
  simpa only [sourceCorrectionMatrix, weightedCorrectionMatrix, sourceUnitDomainEquiv_apply, u] using hcoeff

/-- Lemma 6.7(i): the two correction diagonals agree for every complex potential. -/
theorem sourceLemma6_7_i (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    sourceCorrectionMatrix hp φ n z hz h 0 0 = sourceCorrectionMatrix hp φ n z hz h 1 1 :=
  weightedCorrectionMatrix_diagonal_eq hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h

/-- The common diagonal a_n. -/
def sourceResonantA (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) : ℂ :=
  weightedResonantA hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h

/-- The printed b_n⁺ is entry (1,0) in physical order. -/
def sourceResonantBPlus (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) : ℂ :=
  weightedResonantBPlus hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h

/-- The printed b_n⁻ is entry (0,1) in physical order. -/
def sourceResonantBMinus (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) : ℂ :=
  weightedResonantBMinus hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h

/-- The original resonant matrix in the printed (plus, minus) order. -/
def sourcePrintedResonantMatrix (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    Matrix (Fin 2) (Fin 2) ℂ := (sourceResonantMatrix hp φ n z hz h).submatrix Fin.rev Fin.rev

/-- The exact displayed 2×2 matrix, with the off-diagonals in the source order. -/
theorem sourcePrintedResonantMatrix_form (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    sourcePrintedResonantMatrix hp φ n z hz h =
      !![z-(Real.pi : ℂ)*n-sourceResonantA hp φ n z hz h, -sourceResonantBPlus hp φ n z hz h;
        -sourceResonantBMinus hp φ n z hz h, z-(Real.pi : ℂ)*n-sourceResonantA hp φ n z hz h] := by
  unfold sourcePrintedResonantMatrix sourceResonantMatrix
  rw [weightedResonantMatrix_form]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Reversing both basis orders leaves the actual determinant unchanged. -/
theorem sourcePrintedResonantMatrix_det (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    (sourcePrintedResonantMatrix hp φ n z hz h).det = (sourceResonantMatrix hp φ n z hz h).det := by
  simp only [sourcePrintedResonantMatrix, Matrix.det_fin_two, Matrix.submatrix_apply]
  change sourceResonantMatrix hp φ n z hz h 1 1 * sourceResonantMatrix hp φ n z hz h 0 0 -
    sourceResonantMatrix hp φ n z hz h 1 0 * sourceResonantMatrix hp φ n z hz h 0 1 =
    sourceResonantMatrix hp φ n z hz h 0 0 * sourceResonantMatrix hp φ n z hz h 1 1 -
    sourceResonantMatrix hp φ n z hz h 0 1 * sourceResonantMatrix hp φ n z hz h 1 0
  ring

/-- The scalar determinant equation in the source's a_n and b_n± coefficients. -/
theorem sourceResonantMatrix_det_formula (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    (sourceResonantMatrix hp φ n z hz h).det =
      (z-(Real.pi : ℂ)*n-sourceResonantA hp φ n z hz h)^2 -
        sourceResonantBPlus hp φ n z hz h * sourceResonantBMinus hp φ n z hz h := by
  rw [← sourcePrintedResonantMatrix_det, sourcePrintedResonantMatrix_form, Matrix.det_fin_two]
  simp
  ring

/-- The coefficient equation detects the actual original periodic spectrum. -/
theorem sourceSpectrum_iff_resonantScalarEquation (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    z ∉ sourceResolventSet hp φ ↔
      (z-(Real.pi : ℂ)*n-sourceResonantA hp φ n z hz h)^2 =
        sourceResonantBPlus hp φ n z hz h * sourceResonantBMinus hp φ n z hz h := by
  rw [sourceLemma6_6 hp φ n z hz h,sourceResonantMatrix_det_formula,sub_eq_zero]

end NLS.ZakharovShabat
