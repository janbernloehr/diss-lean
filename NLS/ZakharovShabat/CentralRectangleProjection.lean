import NLS.ZakharovShabat.CentralRectangleSelection
import NLS.ZakharovShabat.RectangleSpectrum

/-!
# Identification of the actual central rectangular spectral projection

An enclosing resolvent circle captures the rectangular integral on the entire
base space. Finite-cluster selection then identifies it with the central
algebraic projection. This proves the rectangular contour formula itself,
including all generalized eigenvectors and the complementary subspace.
-/

noncomputable section
open Complex Set Metric Classical
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual four-edge central resolvent integral equals the whole central algebraic projection. -/
theorem centralRectangleIntegral_eq_centralSpectralProjection (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ resolventSet hp φ) :
    centralRectangleIntegral hp φ N = centralSpectralProjection hp φ N := by
  have hs : rectanglePeriodicSpectrum hp φ (centralLowerCorner N) (centralUpperCorner N) =
      centralPeriodicSpectrum hp φ N := by
    ext a
    rw [mem_rectanglePeriodicSpectrum, centralCorner_openRectangle,
      mem_centralPeriodicSpectrum_iff_open hp φ N hc]
  change resolventRectangleIntegral hp φ (centralLowerCorner N) (centralUpperCorner N) = _
  rw [resolventRectangleIntegral_eq_clusterProjection hp φ _ _
    (neg_le_self (centralCircleRadius_pos N).le) (neg_le_self (Nat.cast_nonneg N))
    (by rwa [centralCorner_boundary]), hs]
  rfl

/-- The actual central rectangular integral is idempotent on the entire base space. -/
theorem centralRectangleIntegral_idempotent (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ resolventSet hp φ) :
    IsIdempotentElem (centralRectangleIntegral hp φ N) := by
  rw [centralRectangleIntegral_eq_centralSpectralProjection hp φ N hc]
  exact centralSpectralProjection_idempotent hp φ N

/-- Its range consists exactly of the full generalized eigenspaces inside the central box. -/
theorem range_centralRectangleIntegral (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ resolventSet hp φ) :
    (centralRectangleIntegral hp φ N).range = periodicClusterSpace hp φ (centralPeriodicSpectrum hp φ N) := by
  rw [centralRectangleIntegral_eq_centralSpectralProjection hp φ N hc]
  exact range_periodicClusterProjection hp φ _

/-- The rank of the actual rectangular integral counts full algebraic multiplicities. -/
theorem finrank_range_centralRectangleIntegral (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ resolventSet hp φ) :
    Module.finrank ℂ (centralRectangleIntegral hp φ N).range =
      ∑ a ∈ centralPeriodicSpectrum hp φ N, periodicAlgebraicMultiplicity hp φ a := by
  rw [centralRectangleIntegral_eq_centralSpectralProjection hp φ N hc]
  exact finrank_range_centralSpectralProjection hp φ N

/-- The actual rectangular contour formula is analytic and has rank `4N+2` on one common counting neighborhood. -/
theorem exists_uniform_centralRectangleProjection (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ N : ℕ, N₀ ≤ N → AnalyticOnNhd ℂ (fun ψ => centralRectangleIntegral hp ψ N) U) ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → centralRectangleBoundary N ⊆ resolventSet hp ψ ∧
        centralRectangleIntegral hp ψ N = centralSpectralProjection hp ψ N ∧
        Module.finrank ℂ (centralRectangleIntegral hp ψ N).range = 4 * N + 2 := by
  obtain ⟨N₀, U, hN₀, ho, hc, hφ, h0, han, h⟩ := exists_uniform_central_multiplicity hp φ
  refine ⟨N₀, U, hN₀, ho, hc, hφ, h0, ?_, ?_⟩
  · intro N hN ψ hψ
    apply (han N hN ψ hψ).congr
    filter_upwards [ho.mem_nhds hψ] with a ha
    exact (centralRectangleIntegral_eq_centralSpectralProjection hp a N (h a ha N hN).1).symm
  · intro ψ hψ N hN
    have he := centralRectangleIntegral_eq_centralSpectralProjection hp ψ N (h ψ hψ N hN).1
    exact ⟨(h ψ hψ N hN).1, he, by rw [he]; exact (h ψ hψ N hN).2.1⟩

end NLS.ZakharovShabat
