import NLS.SequenceSpaces.PairNorm
import NLS.ZakharovShabat.HeightRectangleContour

/-!
# Spectral heights in the dissertation's finite-exponent potential norm

The parameter is now the genuine coefficient component-sum Banach space.
Contractivity of the map to the existing maximum-norm coefficients transfers
resolvent estimates without increasing their constants. Uniform neighborhoods
and analytic actual rectangular projections pull back through the complex
linear norm equivalence. Operators still act on the existing coefficient base
space; Fourier/distribution realization is a separate matter.
-/

noncomputable section
open Complex Set Metric Classical
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The explicit all-exponent resolvent bound in the component-sum potential norm. -/
theorem mem_resolventSet_of_coeffPair_height (hp : p ≠ ⊤) (u : CoeffPair p)
    {M : ℝ} (hu : ‖u‖ ≤ M) {z : ℂ}
    (hz : (1 + 8 * p.toReal * M) ^ p.toReal ≤ |z.im|) :
    z ∈ resolventSet hp (CoeffPair.toMax p u) :=
  mem_resolventSet_of_explicit_height hp _ ((CoeffPair.norm_toMax_le u).trans hu) hz

/-- Spectral values lie strictly inside the explicit strip in the source's finite-`p` pair norm. -/
theorem abs_im_lt_coeffPair_height (hp : p ≠ ⊤) (u : CoeffPair p)
    {z : ℂ} (hz : z ∈ periodicSpectrum hp (CoeffPair.toMax p u)) :
    |z.im| < (1 + 8 * p.toReal * ‖u‖) ^ p.toReal :=
  abs_im_lt_explicit_height hp _ (CoeffPair.norm_toMax_le u) hz

/-- The printed Hilbert height also works in the exact component-sum potential norm. -/
theorem mem_resolventSet_of_coeffPair_hilbert_height (u : CoeffPair 2)
    {M : ℝ} (hu : ‖u‖ ≤ M) {z : ℂ} (hz : (1 + 8 * M) ^ 2 ≤ |z.im|) :
    z ∈ resolventSet (by simp) (CoeffPair.toMax 2 u) :=
  mem_resolventSet_of_hilbert_height _ ((CoeffPair.norm_toMax_le u).trans hu) hz

/-- Strict spectral exclusion at the printed Hilbert horizontal edges. -/
theorem abs_im_lt_coeffPair_hilbert_height (u : CoeffPair 2)
    {z : ℂ} (hz : z ∈ periodicSpectrum (by simp) (CoeffPair.toMax 2 u)) :
    |z.im| < (1 + 8 * ‖u‖) ^ 2 :=
  abs_im_lt_hilbert_height _ (CoeffPair.norm_toMax_le u) hz

/-- Pullback of the counting neighborhood for any uniformly bounded sufficient pair-norm height. -/
theorem exists_uniform_coeffPair_heightRectangleProjection_of_bound (hp : p ≠ ⊤) (u : CoeffPair p)
    (H : CoeffPair p → ℝ) (B : ℝ) (hpos : ∀ v, 0 ≤ H v)
    (hB : ∀ v : CoeffPair p,
      ‖v‖ ≤ (2 : ℝ) ^ (1 / p.toReal) * (‖CoeffPair.toMax p u‖ + 1) → H v ≤ B)
    (hh : ∀ v : CoeffPair p, ∀ z : ℂ, H v ≤ |z.im| → z ∈ resolventSet hp (CoeffPair.toMax p v)) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ u ∈ U ∧ 0 ∈ U ∧
      (∀ N : ℕ, N₀ ≤ N → AnalyticOnNhd ℂ
        (fun v => heightRectangleIntegral hp (CoeffPair.toMax p v) N (H v)) U) ∧
      ∀ v ∈ U, ∀ N : ℕ, N₀ ≤ N →
        RectangleIntegral.boundary (heightLowerCorner N (H v)) (heightUpperCorner N (H v)) ⊆
          resolventSet hp (CoeffPair.toMax p v) ∧
        heightRectangleIntegral hp (CoeffPair.toMax p v) N (H v) =
          centralSpectralProjection hp (CoeffPair.toMax p v) N ∧
        Module.finrank ℂ (heightRectangleIntegral hp (CoeffPair.toMax p v) N (H v)).range = 4 * N + 2 := by
  let e := CoeffPair.toMax p
  have hB' (ψ : PairSpace p) (hψ : ‖ψ‖ ≤ ‖e u‖ + 1) : H (e.symm ψ) ≤ B := by
    apply hB
    exact (CoeffPair.norm_toMax_symm_le hp ψ).trans
      (mul_le_mul_of_nonneg_left hψ (by positivity))
  have hh' (ψ : PairSpace p) (z : ℂ) (hz : H (e.symm ψ) ≤ |z.im|) : z ∈ resolventSet hp ψ := by
    simpa only [e, ContinuousLinearEquiv.apply_symm_apply] using hh (e.symm ψ) z hz
  obtain ⟨N₀, U, hN₀, ho, hc, hu, h0, han, h⟩ := exists_uniform_heightRectangleProjection_of_bound
    hp (e u) (fun ψ => H (e.symm ψ)) B (fun ψ => hpos (e.symm ψ)) hB' hh'
  refine ⟨N₀, e ⁻¹' U, hN₀, ho.preimage e.continuous,
    hc.linear_preimage (e.toLinearMap.restrictScalars ℝ), hu, ?_, ?_, ?_⟩
  · simpa only [mem_preimage, map_zero] using h0
  · intro N hN v hv
    have ha := (han N hN (e v) hv).comp (f := e) (e.toContinuousLinearMap.analyticAt v)
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using! ha
  · intro v hv N hN
    have hvh := h (e v) hv N hN
    rw [e.symm_apply_apply] at hvh
    exact hvh

/-- The printed Hilbert contour formula and rank on an open convex neighborhood in the exact source norm. -/
theorem exists_uniform_coeffPair_hilbert_heightRectangleProjection (u : CoeffPair 2) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair 2), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ u ∈ U ∧ 0 ∈ U ∧
      (∀ N : ℕ, N₀ ≤ N → AnalyticOnNhd ℂ
        (fun v => heightRectangleIntegral (by simp) (CoeffPair.toMax 2 v) N ((1 + 8 * ‖v‖) ^ 2)) U) ∧
      ∀ v ∈ U, ∀ N : ℕ, N₀ ≤ N →
        RectangleIntegral.boundary (heightLowerCorner N ((1 + 8 * ‖v‖) ^ 2))
          (heightUpperCorner N ((1 + 8 * ‖v‖) ^ 2)) ⊆ resolventSet (by simp) (CoeffPair.toMax 2 v) ∧
        heightRectangleIntegral (by simp) (CoeffPair.toMax 2 v) N ((1 + 8 * ‖v‖) ^ 2) =
          centralSpectralProjection (by simp) (CoeffPair.toMax 2 v) N ∧
        Module.finrank ℂ
          (heightRectangleIntegral (by simp) (CoeffPair.toMax 2 v) N ((1 + 8 * ‖v‖) ^ 2)).range = 4 * N + 2 := by
  apply exists_uniform_coeffPair_heightRectangleProjection_of_bound (by simp) u
    (fun v => (1 + 8 * ‖v‖) ^ 2)
    ((1 + 8 * ((2 : ℝ) ^ (1 / (2 : ℝ)) * (‖CoeffPair.toMax 2 u‖ + 1))) ^ 2)
  · intro v
    positivity
  · intro v hv
    norm_num only [ENNReal.toReal_ofNat] at hv
    gcongr
  · intro v z hz
    exact mem_resolventSet_of_coeffPair_hilbert_height v le_rfl hz

/-- All finite exponents have analytic actual contours at the proved height in the source pair norm. -/
theorem exists_uniform_coeffPair_explicit_heightRectangleProjection (hp : p ≠ ⊤) (u : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ u ∈ U ∧ 0 ∈ U ∧
      (∀ N : ℕ, N₀ ≤ N → AnalyticOnNhd ℂ
        (fun v => heightRectangleIntegral hp (CoeffPair.toMax p v) N
          ((1 + 8 * p.toReal * ‖v‖) ^ p.toReal)) U) ∧
      ∀ v ∈ U, ∀ N : ℕ, N₀ ≤ N →
        RectangleIntegral.boundary (heightLowerCorner N ((1 + 8 * p.toReal * ‖v‖) ^ p.toReal))
          (heightUpperCorner N ((1 + 8 * p.toReal * ‖v‖) ^ p.toReal)) ⊆
            resolventSet hp (CoeffPair.toMax p v) ∧
        heightRectangleIntegral hp (CoeffPair.toMax p v) N ((1 + 8 * p.toReal * ‖v‖) ^ p.toReal) =
          centralSpectralProjection hp (CoeffPair.toMax p v) N ∧
        Module.finrank ℂ (heightRectangleIntegral hp (CoeffPair.toMax p v) N
          ((1 + 8 * p.toReal * ‖v‖) ^ p.toReal)).range = 4 * N + 2 := by
  apply exists_uniform_coeffPair_heightRectangleProjection_of_bound hp u
    (fun v => (1 + 8 * p.toReal * ‖v‖) ^ p.toReal)
    ((1 + 8 * p.toReal * ((2 : ℝ) ^ (1 / p.toReal) * (‖CoeffPair.toMax p u‖ + 1))) ^ p.toReal)
  · intro v
    positivity
  · intro v hv
    gcongr
  · intro v z hz
    exact mem_resolventSet_of_coeffPair_height hp v le_rfl hz

end NLS.ZakharovShabat
