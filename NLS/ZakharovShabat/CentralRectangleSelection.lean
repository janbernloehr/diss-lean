import NLS.ZakharovShabat.CentralRectangleContour
import NLS.ZakharovShabat.RectangleRootSelection

/-!
# Central rectangular selection of generalized eigenspaces

The actual four-edge contour fixes all central full root spaces and annihilates
all exterior ones. In particular it absorbs the algebraic central projection,
and its range contains the full central cluster. The whole operator equality
is proved by enclosing-circle comparison in `CentralRectangleProjection`.
-/

noncomputable section
open Complex Set Classical
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The interior determined by the two central corners is exactly the open central rectangle. -/
theorem centralCorner_openRectangle (N : ℕ) :
    Ioo (centralLowerCorner N).re (centralUpperCorner N).re ×ℂ
      Ioo (centralLowerCorner N).im (centralUpperCorner N).im = openCentralRectangle N := by
  ext a
  change ((-centralCircleRadius N < a.re ∧ a.re < centralCircleRadius N) ∧
    (-(N : ℝ) < a.im ∧ a.im < (N : ℝ))) ↔
    (|a.re| < centralCircleRadius N ∧ |a.im| < (N : ℝ))
  rw [abs_lt, abs_lt]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The central rectangular integral selects root-space projections by actual open-box membership. -/
theorem centralRectangleIntegral_mul_projection_eq_ite (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (a : ℂ)
    (hc : centralRectangleBoundary N ⊆ resolventSet hp φ) :
    centralRectangleIntegral hp φ N * periodicSpectralProjection hp φ a =
      if a ∈ openCentralRectangle N then periodicSpectralProjection hp φ a else 0 := by
  rw [centralRectangleIntegral, ← centralCorner_openRectangle]
  exact resolventRectangleIntegral_mul_projection_eq_ite hp φ _ _ a
    (neg_le_self (centralCircleRadius_pos N).le) (neg_le_self (Nat.cast_nonneg N))
    (by rwa [centralCorner_boundary])

/-- On its central algebraic cluster, the actual rectangular contour is the identity. -/
theorem centralRectangleIntegral_mul_centralSpectralProjection (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ resolventSet hp φ) :
    centralRectangleIntegral hp φ N * centralSpectralProjection hp φ N = centralSpectralProjection hp φ N := by
  classical
  rw [centralSpectralProjection, periodicClusterProjection, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [centralRectangleIntegral_mul_projection_eq_ite hp φ N a hc]
  exact if_pos ((mem_centralPeriodicSpectrum_iff_open hp φ N hc a).mp ha).2

/-- Every central generalized vector is in the range of the actual four-edge contour. -/
theorem range_centralSpectralProjection_le_rectangle (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ resolventSet hp φ) :
    (centralSpectralProjection hp φ N).range ≤ (centralRectangleIntegral hp φ N).range := by
  rintro x ⟨y, rfl⟩
  exact ⟨centralSpectralProjection hp φ N y,
    DFunLike.congr_fun (centralRectangleIntegral_mul_centralSpectralProjection hp φ N hc) y⟩

end NLS.ZakharovShabat
