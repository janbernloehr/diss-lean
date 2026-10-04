import NLS.SequenceSpaces.AnalyticSequenceSlice
import NLS.SequenceSpaces.TailSquareDescentCoordinateAnalytic

/-! # Analytic coordinate slices of a sequence-valued tail descent

The descended map is analytic in the full target sequence norm along any
individual coordinate line, on its entire open intersection with the
mixed-coordinate image. This includes both head coordinates and zero tail
squares. Joint analyticity in the source sequence norm is a further step.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
variable [p.HolderTriple p q]

/-- The entire coordinate slice is analytic in the target sequence norm. -/
theorem analyticOnNhd_tailSquareDescent_coordinateSlice (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → Coeff r) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (b : Coeff q × Coeff q) (second : Bool) (k : ℤ) :
    AnalyticOnNhd ℂ (fun t : ℂ => tailSquareDescent S f V (b+pairSingleCLM q second k t))
      ((fun t : ℂ => b+pairSingleCLM q second k t) ⁻¹' (pairMixedSquare S '' V)) := by
  apply analyticOnNhd_sequenceSlice (tailSquareDescent (q := q) S f V)
    (pairMixedSquare (q := q) S '' V) (isOpenMap_pairMixedSquare hp S V hV)
    (continuousOn_tailSquareDescent (q := q) hp S f V hV hf.continuousOn hinv)
    (pairSingleCLM q second k) _ b
  rintro _ ⟨z,hz,rfl⟩ n
  exact analyticAt_tailSquareDescent_coordinate S f V hV hf hinv z hz second k
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) r n)

/-- At every point of the mixed-coordinate image, an individual coordinate
perturbation is analytic in the full sequence norm, without nonvanishing. -/
theorem analyticAt_tailSquareDescent_coordinateSlice (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → Coeff r) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (b : Coeff q × Coeff q) (hb : b ∈ pairMixedSquare S '' V) (second : Bool) (k : ℤ) :
    AnalyticAt ℂ (fun t : ℂ => tailSquareDescent S f V (b+pairSingleCLM q second k t)) 0 :=
  analyticOnNhd_tailSquareDescent_coordinateSlice hp S f V hV hf hinv b second k 0
    (by simpa using hb)

end NLS.Coeff
