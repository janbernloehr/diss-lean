import NLS.ZakharovShabat.RectangleSpectrum
import NLS.ZakharovShabat.HeightSpectralBox

/-!
# Actual contours at norm-dependent spectral heights

The four edges now move to an independent positive height. A global resolvent
strip and the existing central vertical edges make the new boundary admissible.
Its actual integral equals the fixed central projection. Thus even a height
which depends nonanalytically on the potential norm gives an operator-norm
analytic projection on the counting neighborhood.
-/

noncomputable section
open Complex Set Metric Classical
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Lower-left corner at independent height. -/
def heightLowerCorner (N : ℕ) (H : ℝ) : ℂ := ⟨-centralCircleRadius N, -H⟩

/-- Upper-right corner at independent height. -/
def heightUpperCorner (N : ℕ) (H : ℝ) : ℂ := ⟨centralCircleRadius N, H⟩

/-- The filled rectangle has the intended absolute-value inequalities. -/
theorem heightCorner_rectangle (N : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    uIcc (heightLowerCorner N H).re (heightUpperCorner N H).re ×ℂ
      uIcc (heightLowerCorner N H).im (heightUpperCorner N H).im =
        {z : ℂ | |z.re| ≤ centralCircleRadius N ∧ |z.im| ≤ H} := by
  ext z
  change (z.re ∈ uIcc (-centralCircleRadius N) (centralCircleRadius N) ∧
    z.im ∈ uIcc (-H) H) ↔ _
  rw [uIcc_of_le (neg_le_self (centralCircleRadius_pos N).le), uIcc_of_le (neg_le_self hH)]
  change _ ↔ |z.re| ≤ centralCircleRadius N ∧ |z.im| ≤ H
  rw [abs_le, abs_le]
  rfl

/-- The interior has strict inequalities at both coordinates. -/
theorem heightCorner_openRectangle (N : ℕ) (H : ℝ) :
    Ioo (heightLowerCorner N H).re (heightUpperCorner N H).re ×ℂ
      Ioo (heightLowerCorner N H).im (heightUpperCorner N H).im =
        {z : ℂ | |z.re| < centralCircleRadius N ∧ |z.im| < H} := by
  ext z
  change ((-centralCircleRadius N < z.re ∧ z.re < centralCircleRadius N) ∧
    (-H < z.im ∧ z.im < H)) ↔ (|z.re| < centralCircleRadius N ∧ |z.im| < H)
  rw [abs_lt, abs_lt]

/-- Boundary membership retains all four corners of the independent-height box. -/
theorem mem_heightCorner_boundary (N : ℕ) {H : ℝ} (hH : 0 ≤ H) (z : ℂ) :
    z ∈ RectangleIntegral.boundary (heightLowerCorner N H) (heightUpperCorner N H) ↔
      (|z.re| ≤ centralCircleRadius N ∧ |z.im| ≤ H) ∧
        (|z.re| = centralCircleRadius N ∨ |z.im| = H) := by
  change (z.re ∈ uIcc (-centralCircleRadius N) (centralCircleRadius N) ∧
    z.im ∈ uIcc (-H) H ∧
    (z.re = -centralCircleRadius N ∨ z.re = centralCircleRadius N ∨ z.im = -H ∨ z.im = H)) ↔ _
  rw [uIcc_of_le (neg_le_self (centralCircleRadius_pos N).le), uIcc_of_le (neg_le_self hH)]
  change ((-centralCircleRadius N ≤ z.re ∧ z.re ≤ centralCircleRadius N) ∧
    (-H ≤ z.im ∧ z.im ≤ H) ∧ _) ↔ _
  rw [abs_le, abs_le, abs_eq (centralCircleRadius_pos N).le, abs_eq hH]
  tauto

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual normalized four-edge resolvent integral at the specified height. -/
def heightRectangleIntegral (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (H : ℝ) :
    PairSpace p →L[ℂ] PairSpace p :=
  resolventRectangleIntegral hp φ (heightLowerCorner N H) (heightUpperCorner N H)

/-- The old vertical boundary and a global high strip make the moved contour admissible. -/
theorem heightCorner_boundary_subset_resolvent (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    {H : ℝ} (hH : 0 ≤ H) (hHN : H ≤ (N : ℝ))
    (hc : centralRectangleBoundary N ⊆ resolventSet hp φ)
    (hh : ∀ z : ℂ, H ≤ |z.im| → z ∈ resolventSet hp φ) :
    RectangleIntegral.boundary (heightLowerCorner N H) (heightUpperCorner N H) ⊆
      resolventSet hp φ := by
  intro z hz
  obtain ⟨hbox, hre | him⟩ := (mem_heightCorner_boundary N hH z).mp hz
  · apply hc
    rw [mem_centralRectangleBoundary]
    exact ⟨⟨hbox.1, hbox.2.trans hHN⟩, Or.inl hre⟩
  · exact hh z him.ge

/-- A global high strip equates the open rectangular selection with the mixed-boundary box. -/
theorem rectanglePeriodicSpectrum_heightCorners (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (H : ℝ)
    (hh : ∀ z : ℂ, H ≤ |z.im| → z ∈ resolventSet hp φ) :
    rectanglePeriodicSpectrum hp φ (heightLowerCorner N H) (heightUpperCorner N H) =
      heightPeriodicSpectrum hp φ N H := by
  ext z
  rw [mem_rectanglePeriodicSpectrum, mem_heightPeriodicSpectrum, heightCorner_openRectangle]
  constructor
  · rintro ⟨hz, hre, him⟩
    exact ⟨hz, hre, him.le⟩
  · rintro ⟨hz, hre, _⟩
    exact ⟨hz, hre, lt_of_not_ge (fun hi => hz (hh z hi))⟩

/-- The actual moved contour agrees with the fixed central algebraic projection on the whole space. -/
theorem heightRectangleIntegral_eq_centralSpectralProjection (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    {H : ℝ} (hH : 0 ≤ H) (hHN : H ≤ (N : ℝ))
    (hc : centralRectangleBoundary N ⊆ resolventSet hp φ)
    (hh : ∀ z : ℂ, H ≤ |z.im| → z ∈ resolventSet hp φ) :
    heightRectangleIntegral hp φ N H = centralSpectralProjection hp φ N := by
  rw [heightRectangleIntegral, resolventRectangleIntegral_eq_clusterProjection hp φ _ _
    (neg_le_self (centralCircleRadius_pos N).le) (neg_le_self hH)
    (heightCorner_boundary_subset_resolvent hp φ N hH hHN hc hh),
    rectanglePeriodicSpectrum_heightCorners hp φ N H hh,
    heightPeriodicSpectrum_eq_central hp φ N hHN
      (fun z hz => (lt_of_not_ge (fun hi => hz (hh z hi))).le)]
  rfl

/-- Uniformly bounded sufficient heights give analytic actual contours and the exact central rank.
The height function itself need not be continuous or analytic. -/
theorem exists_uniform_heightRectangleProjection_of_bound (hp : p ≠ ⊤) (φ : PairSpace p)
    (H : PairSpace p → ℝ) (B : ℝ) (hpos : ∀ ψ, 0 ≤ H ψ)
    (hB : ∀ ψ : PairSpace p, ‖ψ‖ ≤ ‖φ‖ + 1 → H ψ ≤ B)
    (hh : ∀ ψ : PairSpace p, ∀ z : ℂ, H ψ ≤ |z.im| → z ∈ resolventSet hp ψ) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ N : ℕ, N₀ ≤ N → AnalyticOnNhd ℂ (fun ψ => heightRectangleIntegral hp ψ N (H ψ)) U) ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        RectangleIntegral.boundary (heightLowerCorner N (H ψ)) (heightUpperCorner N (H ψ)) ⊆
          resolventSet hp ψ ∧
        heightRectangleIntegral hp ψ N (H ψ) = centralSpectralProjection hp ψ N ∧
        Module.finrank ℂ (heightRectangleIntegral hp ψ N (H ψ)).range = 4 * N + 2 := by
  obtain ⟨K, U, hK, ho, hc, hφ, h0, han, h⟩ := exists_uniform_central_multiplicity hp φ
  obtain ⟨L, hL⟩ := exists_nat_ge B
  let V := U ∩ ball 0 (‖φ‖ + 1)
  have hvo : IsOpen V := ho.inter isOpen_ball
  have hheight (ψ : PairSpace p) (hψ : ψ ∈ V) (N : ℕ) (hN : max K L ≤ N) : H ψ ≤ (N : ℝ) := by
    have hNL : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_max_right K L).trans hN
    exact (hB ψ (mem_ball_zero_iff.mp hψ.2).le).trans (hL.trans hNL)
  have he (ψ : PairSpace p) (hψ : ψ ∈ V) (N : ℕ) (hN : max K L ≤ N) :
      heightRectangleIntegral hp ψ N (H ψ) = centralSpectralProjection hp ψ N :=
    heightRectangleIntegral_eq_centralSpectralProjection hp ψ N (hpos ψ) (hheight ψ hψ N hN)
      (h ψ hψ.1 N ((le_max_left _ _).trans hN)).1 (hh ψ)
  refine ⟨max K L, V, lt_of_lt_of_le hK (le_max_left _ _), hvo,
    hc.inter (convex_ball _ _), ⟨hφ, ?_⟩, ⟨h0, ?_⟩, ?_, ?_⟩
  · simpa only [mem_ball, dist_zero_right] using lt_add_one ‖φ‖
  · simp only [mem_ball, dist_self]
    positivity
  · intro N hN ψ hψ
    apply (han N ((le_max_left _ _).trans hN) ψ hψ.1).congr
    filter_upwards [hvo.mem_nhds hψ] with a ha
    exact (he a ha N hN).symm
  · intro ψ hψ N hN
    refine ⟨heightCorner_boundary_subset_resolvent hp ψ N (hpos ψ) (hheight ψ hψ N hN)
      (h ψ hψ.1 N ((le_max_left _ _).trans hN)).1 (hh ψ), he ψ hψ N hN, ?_⟩
    rw [he ψ hψ N hN]
    exact (h ψ hψ.1 N ((le_max_left _ _).trans hN)).2.1

/-- Actual contours at the printed Hilbert height are analytic and have rank `4N+2`, uniformly. -/
theorem exists_uniform_hilbert_heightRectangleProjection (φ : PairSpace 2) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace 2), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ N : ℕ, N₀ ≤ N → AnalyticOnNhd ℂ
        (fun ψ => heightRectangleIntegral (by norm_num) ψ N ((1 + 8 * ‖ψ‖) ^ 2)) U) ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        RectangleIntegral.boundary (heightLowerCorner N ((1 + 8 * ‖ψ‖) ^ 2))
          (heightUpperCorner N ((1 + 8 * ‖ψ‖) ^ 2)) ⊆ resolventSet (by norm_num) ψ ∧
        heightRectangleIntegral (by norm_num) ψ N ((1 + 8 * ‖ψ‖) ^ 2) =
          centralSpectralProjection (by norm_num) ψ N ∧
        Module.finrank ℂ (heightRectangleIntegral (by norm_num) ψ N ((1 + 8 * ‖ψ‖) ^ 2)).range =
          4 * N + 2 := by
  apply exists_uniform_heightRectangleProjection_of_bound (by norm_num) φ
    (fun ψ => (1 + 8 * ‖ψ‖) ^ 2) ((1 + 8 * (‖φ‖ + 1)) ^ 2)
  · intro ψ
    positivity
  · intro ψ hψ
    gcongr
  · intro ψ z hz
    exact mem_resolventSet_of_hilbert_height ψ le_rfl hz

/-- The explicit all-exponent height also gives actual analytic contours of central rank `4N+2`. -/
theorem exists_uniform_explicit_heightRectangleProjection (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ N : ℕ, N₀ ≤ N → AnalyticOnNhd ℂ
        (fun ψ => heightRectangleIntegral hp ψ N ((1 + 8 * p.toReal * ‖ψ‖) ^ p.toReal)) U) ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        RectangleIntegral.boundary (heightLowerCorner N ((1 + 8 * p.toReal * ‖ψ‖) ^ p.toReal))
          (heightUpperCorner N ((1 + 8 * p.toReal * ‖ψ‖) ^ p.toReal)) ⊆ resolventSet hp ψ ∧
        heightRectangleIntegral hp ψ N ((1 + 8 * p.toReal * ‖ψ‖) ^ p.toReal) =
          centralSpectralProjection hp ψ N ∧
        Module.finrank ℂ (heightRectangleIntegral hp ψ N ((1 + 8 * p.toReal * ‖ψ‖) ^ p.toReal)).range =
          4 * N + 2 := by
  apply exists_uniform_heightRectangleProjection_of_bound hp φ
    (fun ψ => (1 + 8 * p.toReal * ‖ψ‖) ^ p.toReal) ((1 + 8 * p.toReal * (‖φ‖ + 1)) ^ p.toReal)
  · intro ψ
    positivity
  · intro ψ hψ
    gcongr
  · intro ψ z hz
    exact mem_resolventSet_of_explicit_height hp ψ le_rfl hz

end NLS.ZakharovShabat
