import NLS.ZakharovShabat.ResolventRectangle
import NLS.ZakharovShabat.CentralDeformation

/-!
# The four-edge contour on the central spectral rectangle

The corner-based boundary is exactly the existing central rectangle boundary,
including all four corners. Its actual normalized resolvent integral is compact
and factors through the domain, uniformly on the existing counting neighborhood.
Equality with the whole central algebraic projection is proved in `CentralRectangleProjection`.
-/

noncomputable section
open Complex Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Lower-left corner of the height-`N` central box. -/
def centralLowerCorner (N : ℕ) : ℂ := ⟨-centralCircleRadius N, -(N : ℝ)⟩

/-- Upper-right corner of the height-`N` central box. -/
def centralUpperCorner (N : ℕ) : ℂ := ⟨centralCircleRadius N, (N : ℝ)⟩

/-- The closed integration rectangle is exactly the previously used closed central box. -/
theorem centralCorner_rectangle (N : ℕ) :
    uIcc (centralLowerCorner N).re (centralUpperCorner N).re ×ℂ
      uIcc (centralLowerCorner N).im (centralUpperCorner N).im = closedCentralRectangle N := by
  have ha := (centralCircleRadius_pos N).le
  have hN := Nat.cast_nonneg (α := ℝ) N
  ext ζ
  change (ζ.re ∈ uIcc (-centralCircleRadius N) (centralCircleRadius N) ∧
    ζ.im ∈ uIcc (-(N : ℝ)) (N : ℝ)) ↔
    (|ζ.re| ≤ centralCircleRadius N ∧ |ζ.im| ≤ (N : ℝ))
  rw [uIcc_of_le (neg_le_self ha), uIcc_of_le (neg_le_self hN), abs_le, abs_le]
  rfl

/-- All four oriented edges, including the corners, give precisely the central contour boundary. -/
theorem centralCorner_boundary (N : ℕ) :
    RectangleIntegral.boundary (centralLowerCorner N) (centralUpperCorner N) = centralRectangleBoundary N := by
  have ha := (centralCircleRadius_pos N).le
  have hN := Nat.cast_nonneg (α := ℝ) N
  ext ζ
  rw [mem_centralRectangleBoundary]
  change (ζ.re ∈ uIcc (-centralCircleRadius N) (centralCircleRadius N) ∧
    ζ.im ∈ uIcc (-(N : ℝ)) (N : ℝ) ∧
    (ζ.re = -centralCircleRadius N ∨ ζ.re = centralCircleRadius N ∨
      ζ.im = -(N : ℝ) ∨ ζ.im = (N : ℝ))) ↔ _
  rw [uIcc_of_le (neg_le_self ha), uIcc_of_le (neg_le_self hN)]
  change ((-centralCircleRadius N ≤ ζ.re ∧ ζ.re ≤ centralCircleRadius N) ∧
    (-(N : ℝ) ≤ ζ.im ∧ ζ.im ≤ (N : ℝ)) ∧ _) ↔
    (|ζ.re| ≤ centralCircleRadius N ∧ |ζ.im| ≤ (N : ℝ)) ∧
      (|ζ.re| = centralCircleRadius N ∨ |ζ.im| = (N : ℝ))
  rw [abs_le, abs_le, abs_eq ha, abs_eq hN]
  tauto

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual normalized four-edge resolvent integral around the central box. -/
def centralRectangleIntegral (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) : PairSpace p →L[ℂ] PairSpace p :=
  resolventRectangleIntegral hp φ (centralLowerCorner N) (centralUpperCorner N)

/-- Central boundary admissibility provides a domain-valued factorization. -/
theorem centralRectangleIntegral_eq_inclusion (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ resolventSet hp φ) :
    centralRectangleIntegral hp φ N = domainInclusion.comp
      (resolventRectangleIntegralToDomain hp φ (centralLowerCorner N) (centralUpperCorner N)) :=
  resolventRectangleIntegral_eq_inclusion hp φ _ _ (by rwa [centralCorner_boundary])

/-- The actual central rectangular contour integral is a compact operator. -/
theorem isCompactOperator_centralRectangleIntegral (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ resolventSet hp φ) :
    IsCompactOperator (centralRectangleIntegral hp φ N) :=
  isCompactOperator_resolventRectangleIntegral hp φ _ _ (by rwa [centralCorner_boundary])

/-- One common neighborhood admits every sufficiently large rectangular contour, in the domain norm. -/
theorem exists_uniform_centralRectangleIntegral (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        RectangleIntegral.Integrable (resolventToDomain hp ψ) (centralLowerCorner N) (centralUpperCorner N) ∧
        centralRectangleIntegral hp ψ N = domainInclusion.comp
          (resolventRectangleIntegralToDomain hp ψ (centralLowerCorner N) (centralUpperCorner N)) ∧
        IsCompactOperator (centralRectangleIntegral hp ψ N) := by
  obtain ⟨N₀, U, hN₀, ho, hc, hφ, h0, h⟩ := exists_uniform_centralCircle hp φ
  refine ⟨N₀, U, hN₀, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ N hN
  have hb := (h ψ hψ N hN).1
  exact ⟨rectangleIntegrable_resolventToDomain hp ψ _ _ (by rwa [centralCorner_boundary]),
    centralRectangleIntegral_eq_inclusion hp ψ N hb, isCompactOperator_centralRectangleIntegral hp ψ N hb⟩

end NLS.ZakharovShabat
