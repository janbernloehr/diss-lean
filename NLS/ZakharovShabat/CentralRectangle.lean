import NLS.ZakharovShabat.SpectralLocalization

/-!
# The central spectral rectangle and its admissible boundary

The box in Corollary 3.5 is strict in the real coordinate but closed in the
imaginary coordinate. For contour integration we also need the fully closed
rectangle, its interior, and all four boundary edges. The retained uniform
height bound proves resolvent inclusion even on the horizontal edges.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal

namespace NLS.ZakharovShabat

/-- The fully closed central rectangle. -/
def closedCentralRectangle (N : ℕ) : Set ℂ :=
  {z | |z.re| ≤ (N : ℝ) * Real.pi + Real.pi / 2 ∧ |z.im| ≤ (N : ℝ)}

/-- The open central rectangle. -/
def openCentralRectangle (N : ℕ) : Set ℂ :=
  {z | |z.re| < (N : ℝ) * Real.pi + Real.pi / 2 ∧ |z.im| < (N : ℝ)}

/-- The four edges, including all corners, of the central rectangle. -/
def centralRectangleBoundary (N : ℕ) : Set ℂ :=
  closedCentralRectangle N \ openCentralRectangle N

/-- Boundary points lie on at least one of the four edges. -/
theorem mem_centralRectangleBoundary (N : ℕ) (z : ℂ) :
    z ∈ centralRectangleBoundary N ↔ z ∈ closedCentralRectangle N ∧
      (|z.re| = (N : ℝ) * Real.pi + Real.pi / 2 ∨ |z.im| = (N : ℝ)) := by
  change (_ ∧ _) ∧ ¬(_ ∧ _) ↔ (_ ∧ _) ∧ (_ ∨ _)
  constructor
  · rintro ⟨⟨hre, him⟩, h⟩
    refine ⟨⟨hre, him⟩, ?_⟩
    by_cases he : |z.re| = (N : ℝ) * Real.pi + Real.pi / 2
    · exact Or.inl he
    · exact Or.inr (le_antisymm him (le_of_not_gt fun hi => h ⟨lt_of_le_of_ne hre he, hi⟩))
  · rintro ⟨⟨hre, him⟩, he | he⟩ <;> exact ⟨⟨hre, him⟩, by rintro ⟨h₁, h₂⟩; linarith⟩

theorem isOpen_openCentralRectangle (N : ℕ) : IsOpen (openCentralRectangle N) :=
  (isOpen_lt continuous_re.abs continuous_const).inter
    (isOpen_lt continuous_im.abs continuous_const)

theorem isClosed_closedCentralRectangle (N : ℕ) : IsClosed (closedCentralRectangle N) :=
  (isClosed_le continuous_re.abs continuous_const).inter
    (isClosed_le continuous_im.abs continuous_const)

/-- The closed rectangle is bounded, hence compact. -/
theorem isCompact_closedCentralRectangle (N : ℕ) : IsCompact (closedCentralRectangle N) := by
  apply (isCompact_closedBall (0 : ℂ) ((N : ℝ) * Real.pi + Real.pi / 2 + N)).of_isClosed_subset
    (isClosed_closedCentralRectangle N)
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  exact (norm_le_abs_re_add_abs_im z).trans (add_le_add hz.1 hz.2)

theorem isCompact_centralRectangleBoundary (N : ℕ) : IsCompact (centralRectangleBoundary N) :=
  (isCompact_closedCentralRectangle N).diff (isOpen_openCentralRectangle N)

/-- Each vertical edge belongs to the punctured strip with edge index `±N`. -/
theorem vertical_edge_mem_strip (N : ℕ) {r : ℝ} (hrπ : r ≤ Real.pi / 4)
    {z : ℂ} (hz : |z.re| = (N : ℝ) * Real.pi + Real.pi / 2) :
    ∃ n : ℤ, n.natAbs = N ∧ z ∈ verticalStrip n r := by
  have hnorm (n : ℤ) (he : |z.re - Real.pi * n| = Real.pi / 2) :
      z ∈ verticalStrip n r := by
    refine ⟨he.le, ?_⟩
    have h := Complex.abs_re_le_norm (z - (Real.pi : ℂ) * n)
    have he' : |(z - (Real.pi : ℂ) * n).re| = Real.pi / 2 := by simpa using he
    rw [he'] at h
    exact (show r ≤ Real.pi / 2 by linarith [Real.pi_pos]).trans h
  by_cases hsign : 0 ≤ z.re
  · rw [abs_of_nonneg hsign] at hz
    refine ⟨(N : ℤ), by simp, hnorm _ ?_⟩
    have he : z.re - Real.pi * (N : ℤ) = Real.pi / 2 := by push_cast; nlinarith
    rw [he, abs_of_pos Real.pi_div_two_pos]
  · rw [abs_of_neg (lt_of_not_ge hsign)] at hz
    refine ⟨-(N : ℤ), by simp, hnorm _ ?_⟩
    have he : z.re - Real.pi * (-(N : ℤ)) = -(Real.pi / 2) := by push_cast; nlinarith
    simp only [Int.cast_neg]
    rw [he, abs_neg, abs_of_pos Real.pi_div_two_pos]

/-- Every boundary point is at the central height or in an edge-index strip. -/
theorem centralRectangleBoundary_height_or_strip (N : ℕ) {r : ℝ} (hrπ : r ≤ Real.pi / 4)
    {z : ℂ} (hz : z ∈ centralRectangleBoundary N) :
    |z.im| = (N : ℝ) ∨ ∃ n : ℤ, n.natAbs = N ∧ z ∈ verticalStrip n r := by
  rcases ((mem_centralRectangleBoundary N z).mp hz).2 with hre | him
  · exact Or.inr (vertical_edge_mem_strip N hrπ hre)
  · exact Or.inl him

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One neighborhood makes every sufficiently large central rectangle boundary
admissible, simultaneously with its exterior and all farther spectral circles. -/
theorem exists_uniform_centralRectangle_resolvent (hp : p ≠ ⊤) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) :
    ∃ N : ℕ, ∃ U : Set (PairSpace p), 0 < N ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ M : ℕ, N ≤ M →
        centralRectangleBoundary M ⊆ resolventSet hp ψ ∧
        spectralExterior M r ⊆ resolventSet hp ψ ∧
        ∀ n : ℤ, M ≤ n.natAbs → sphere ((Real.pi : ℂ) * n) r ⊆ resolventSet hp ψ := by
  obtain ⟨N, U, hN, ho, hconv, hφ, h0, hb⟩ := exists_uniform_height_and_strips hp φ hr hrπ
  refine ⟨N, U, hN, ho, hconv, hφ, h0, ?_⟩
  intro ψ hψ M hM
  have hNM : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases centralRectangleBoundary_height_or_strip M hrπ hz with him | ⟨n, hn, hstrip⟩
    · exact (hb ψ hψ).1 z (by rw [him]; exact hNM)
    · exact (hb ψ hψ).2 n (by omega) hstrip
  · intro z hz
    rcases spectralExterior_height_or_strip M hrπ hz with him | ⟨n, hn, hstrip⟩
    · exact (hb ψ hψ).1 z (hNM.trans him.le)
    · exact (hb ψ hψ).2 n (hM.trans hn) hstrip
  · intro n hn z hz
    exact (hb ψ hψ).2 n (hM.trans hn) (sphere_subset_verticalStrip n hrπ hz)

/-- If the boundary is in the resolvent set, closing the central box adds no spectrum. -/
theorem periodicSpectrum_inter_closedCentralRectangle (hp : p ≠ ⊤) (φ : PairSpace p)
    (N : ℕ) (hc : centralRectangleBoundary N ⊆ resolventSet hp φ) :
    periodicSpectrum hp φ ∩ closedCentralRectangle N = periodicSpectrum hp φ ∩ centralSpectralBox N := by
  ext z
  constructor
  · rintro ⟨hz, hre, him⟩
    refine ⟨hz, ?_, him⟩
    by_contra h
    exact hz (hc ((mem_centralRectangleBoundary N z).mpr
      ⟨⟨hre, him⟩, Or.inl (le_antisymm hre (le_of_not_gt h))⟩))
  · rintro ⟨hz, hre, him⟩
    exact ⟨hz, hre.le, him⟩

/-- The horizontal edges also add no spectrum under the same boundary hypothesis. -/
theorem periodicSpectrum_inter_openCentralRectangle (hp : p ≠ ⊤) (φ : PairSpace p)
    (N : ℕ) (hc : centralRectangleBoundary N ⊆ resolventSet hp φ) :
    periodicSpectrum hp φ ∩ openCentralRectangle N = periodicSpectrum hp φ ∩ centralSpectralBox N := by
  ext z
  constructor
  · rintro ⟨hz, hre, him⟩
    exact ⟨hz, hre, him.le⟩
  · rintro ⟨hz, hre, him⟩
    refine ⟨hz, hre, ?_⟩
    by_contra h
    exact hz (hc ((mem_centralRectangleBoundary N z).mpr
      ⟨⟨hre.le, him⟩, Or.inr (le_antisymm him (le_of_not_gt h))⟩))

end NLS.ZakharovShabat
