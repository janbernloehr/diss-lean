import NLS.ComplexAnalysis.BanachHolomorphicAnalytic
import NLS.SequenceSpaces.TailSquareDescentFrechet

/-! # Joint analyticity of the tail-square descent

The sign-invariant descent is analytic jointly in the full mixed sequence
norm. The target may be any Banach coefficient space, including `l∞`.
Zero tail entries require no additional hypothesis.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
variable [p.HolderTriple p q]

/-- The continuous tail-square descent has a convergent Banach power series
at every point of its open mixed-coordinate domain. -/
theorem analyticOnNhd_tailSquareDescent (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → Coeff r) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z) :
    AnalyticOnNhd ℂ (tailSquareDescent (q := q) S f V) (pairMixedSquare S '' V) :=
  ComplexAnalysis.analyticOnNhd_of_complexDifferentiableOn _ _ (isOpenMap_pairMixedSquare hp S V hV)
    (differentiableOn_tailSquareDescent hp S f V hV hf hinv)

end NLS.Coeff
