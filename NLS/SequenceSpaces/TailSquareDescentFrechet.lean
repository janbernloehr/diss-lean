import NLS.ComplexAnalysis.AnalyticLineFrechet
import NLS.SequenceSpaces.TailSquareDescentAnalyticLine

/-! # Fréchet differentiability of the tail-square descent

The continuous sign-invariant descent is complex Fréchet differentiable
and `C¹` in the full mixed sequence norm. This includes zero tail entries
and arbitrary directions, with no finite-support restriction.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
variable [p.HolderTriple p q]

/-- The descended sequence map has a complex Fréchet derivative everywhere
in its open mixed-coordinate domain. The target exponent may be infinite. -/
theorem differentiableOn_tailSquareDescent (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → Coeff r) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z) :
    DifferentiableOn ℂ (tailSquareDescent (q := q) S f V) (pairMixedSquare S '' V) :=
  ComplexAnalysis.differentiableOn_of_analyticLines _ _ (isOpenMap_pairMixedSquare hp S V hV)
    (continuousOn_tailSquareDescent hp S f V hV hf.continuousOn hinv)
    (fun b _ d => analyticOnNhd_tailSquareDescent_line hp S f V hV hf hinv b d)

/-- The Fréchet derivative of the descended map is continuous in operator norm. -/
theorem contDiffOn_one_tailSquareDescent (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → Coeff r) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z) :
    ContDiffOn ℂ 1 (tailSquareDescent (q := q) S f V) (pairMixedSquare S '' V) :=
  ComplexAnalysis.contDiffOn_one_of_differentiableOn _ (isOpenMap_pairMixedSquare hp S V hV)
    (differentiableOn_tailSquareDescent hp S f V hV hf hinv)

end NLS.Coeff
