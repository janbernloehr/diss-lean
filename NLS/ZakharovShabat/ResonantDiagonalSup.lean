import NLS.ZakharovShabat.ResonantDiagonalEstimate

/-!
# The full-strip supremum of the diagonal coefficient

This is the actual supremum over the unbounded closed strip, using the total
analytic coefficient. The uniform row estimate proves it finite and bounds
it by the same parameter-independent reciprocal sum.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source's `|a_n|_{U_n}`, defined from the actual analytic extension. -/
def resonantDiagonalSup (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : ℝ :=
  sSup ((fun z : ℂ => ‖weightedResonantAExtension hp w φ n z‖) '' resonantStrip n)

/-- A uniform pointwise bound proves boundedness of the full-strip image. -/
theorem bddAbove_resonantDiagonal_image (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (B : ℝ)
    (hb : ∀ z ∈ resonantStrip n, ‖weightedResonantAExtension hp w φ n z‖ ≤ B) :
    BddAbove ((fun z : ℂ => ‖weightedResonantAExtension hp w φ n z‖) '' resonantStrip n) := by
  refine ⟨B, ?_⟩
  rintro _ ⟨z,hz,rfl⟩
  exact hb z hz

/-- The supremum obeys every uniform pointwise bound. -/
theorem resonantDiagonalSup_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (B : ℝ)
    (hb : ∀ z ∈ resonantStrip n, ‖weightedResonantAExtension hp w φ n z‖ ≤ B) :
    resonantDiagonalSup hp w φ n ≤ B := by
  unfold resonantDiagonalSup
  have hne : ((fun z : ℂ => ‖weightedResonantAExtension hp w φ n z‖) '' resonantStrip n).Nonempty :=
    ⟨_, (Real.pi : ℂ)*n, center_mem_resonantStrip n, rfl⟩
  apply csSup_le hne
  rintro _ ⟨z,hz,rfl⟩
  exact hb z hz

/-- On a bounded strip image the supremum dominates every actual value. -/
theorem norm_resonantAExtension_le_sup (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ)
    (hb : BddAbove ((fun z : ℂ => ‖weightedResonantAExtension hp w φ n z‖) '' resonantStrip n))
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedResonantAExtension hp w φ n z‖ ≤ resonantDiagonalSup hp w φ n :=
  le_csSup hb ⟨z,hz,rfl⟩

/-- The actual strip suprema have the diagonal row bound uniformly on a potential neighborhood. -/
theorem exists_uniform_resonantDiagonalSup (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        0 ≤ resonantDiagonalSup hp w ψ n ∧
        resonantDiagonalSup hp w ψ n ≤ resonantDiagonalBound hp w ψ n ∧
        ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
          ∃ h : ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1,
            ‖weightedResonantA hp w ψ n z hz h‖ ≤ resonantDiagonalSup hp w ψ n := by
  obtain ⟨N, hN, U, ho, hc, hφ, h0, hb⟩ := exists_uniform_resonantDiagonalBound hp w φ
  refine ⟨N, hN, U, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ n hn
  have hpoint (z : ℂ) (hz : z ∈ resonantStrip n) :
      ‖weightedResonantAExtension hp w ψ n z‖ ≤ resonantDiagonalBound hp w ψ n := by
    obtain ⟨_, _, h⟩ := hb ψ hψ n hn z hz
    exact h
  have hbounded := bddAbove_resonantDiagonal_image hp w ψ n _ hpoint
  have hvalue := norm_resonantAExtension_le_sup hp w ψ n hbounded
  refine ⟨(norm_nonneg _).trans (hvalue _ (center_mem_resonantStrip n)),
    resonantDiagonalSup_le hp w ψ n _ hpoint, ?_⟩
  intro z hz
  obtain ⟨h, _, _⟩ := hb ψ hψ n hn z hz
  refine ⟨h, ?_⟩
  rw [← weightedResonantAExtension_eq hp w ψ n z hz h]
  exact hvalue z hz

end NLS.ZakharovShabat
