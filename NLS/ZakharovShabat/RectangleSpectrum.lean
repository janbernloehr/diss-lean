import NLS.ZakharovShabat.RectangleCircleComparison
import NLS.ZakharovShabat.CentralDeformation

/-!
# Whole spectral projection for an arbitrary rectangular contour

Every ordered rectangle with resolvent boundary has a finite enclosed spectral
set. An enclosing resolvent circle identifies the actual four-edge integral
with the full algebraic projection onto that set. No assumption on the
resolvent inside the rectangle is needed.
-/

noncomputable section
open Complex Set Metric Classical
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite periodic spectrum in the interior of a rectangle. -/
def rectanglePeriodicSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ) : Finset ℂ :=
  (finite_periodicSpectrum_inter_of_isBounded hp φ
    ((isBounded_Ioo z.re w.re).reProdIm (isBounded_Ioo z.im w.im))).toFinset

@[simp] theorem mem_rectanglePeriodicSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (z w a : ℂ) :
    a ∈ rectanglePeriodicSpectrum hp φ z w ↔
      a ∈ periodicSpectrum hp φ ∧ a ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im :=
  Set.Finite.mem_toFinset _

/-- An admissible boundary makes the open and closed rectangular spectral selections agree. -/
theorem mem_rectanglePeriodicSpectrum_iff_closed (hp : p ≠ ⊤) (φ : PairSpace p) (z w a : ℂ)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) :
    a ∈ rectanglePeriodicSpectrum hp φ z w ↔
      a ∈ periodicSpectrum hp φ ∧ a ∈ uIcc z.re w.re ×ℂ uIcc z.im w.im := by
  rw [mem_rectanglePeriodicSpectrum]
  constructor
  · rintro ⟨ha, hr, hi⟩
    exact ⟨ha, Icc_subset_uIcc ⟨hr.1.le, hr.2.le⟩, Icc_subset_uIcc ⟨hi.1.le, hi.2.le⟩⟩
  · rintro ⟨ha, hbox⟩
    refine ⟨ha, ?_⟩
    by_contra ho
    exact ha (hc (RectangleIntegral.mem_boundary_of_mem_rectangle_of_not_mem_open hre him hbox ho))

/-- Every bounded set is enclosed by a sufficiently large admissible central circle. -/
theorem exists_enclosing_resolvent_circle (hp : p ≠ ⊤) (φ : PairSpace p)
    {s : Set ℂ} (hs : Bornology.IsBounded s) :
    ∃ r : ℝ, 0 < r ∧ sphere 0 r ⊆ resolventSet hp φ ∧ s ⊆ ball 0 r := by
  obtain ⟨R, hR⟩ := hs.subset_ball (0 : ℂ)
  obtain ⟨L, hL⟩ := exists_nat_ge R
  obtain ⟨K₀, U, _, _, _, hφ, _, h⟩ := exists_uniform_centralCircle hp φ
  let K := max K₀ L
  have hLK : (L : ℝ) ≤ (K : ℝ) := by exact_mod_cast (le_max_right K₀ L)
  have hrad : R ≤ centralCircleRadius K := by
    have hK := Nat.cast_nonneg (α := ℝ) K
    have hπ := Real.one_le_pi_div_two
    unfold centralCircleRadius
    nlinarith
  exact ⟨centralCircleRadius K, centralCircleRadius_pos K,
    (h φ hφ K (le_max_left _ _)).2.1, hR.trans (ball_subset_ball hrad)⟩

/-- The actual rectangular integral is the whole algebraic projection onto its enclosed spectrum. -/
theorem resolventRectangleIntegral_eq_clusterProjection (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) :
    resolventRectangleIntegral hp φ z w =
      periodicClusterProjection hp φ (rectanglePeriodicSpectrum hp φ z w) := by
  obtain ⟨r, hr, hC, hb⟩ := exists_enclosing_resolvent_circle hp φ
    ((isCompact_uIcc (a := z.re) (b := w.re)).isBounded.reProdIm
      (isCompact_uIcc (a := z.im) (b := w.im)).isBounded)
  have he : (enclosedPeriodicSpectrum hp φ 0 r).filter
      (fun a => a ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) = rectanglePeriodicSpectrum hp φ z w := by
    ext a
    rw [Finset.mem_filter, mem_enclosedPeriodicSpectrum, mem_rectanglePeriodicSpectrum]
    constructor
    · rintro ⟨⟨ha, _⟩, ho⟩
      exact ⟨ha, ho⟩
    · rintro ⟨ha, ho⟩
      exact ⟨⟨ha, hb ⟨Icc_subset_uIcc ⟨ho.1.1.le, ho.1.2.le⟩,
        Icc_subset_uIcc ⟨ho.2.1.le, ho.2.2.le⟩⟩⟩, ho⟩
  rw [← resolventRectangleIntegral_mul_enclosing_circle hp φ z w 0 r hr.le hc hC hb,
    resolventCircleIntegral_eq_clusterProjection hp φ 0 r hr.le hC,
    resolventRectangleIntegral_mul_cluster hp φ z w hre him hc, he]

/-- Every ordered admissible rectangular integral is idempotent. -/
theorem resolventRectangleIntegral_idempotent (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) :
    IsIdempotentElem (resolventRectangleIntegral hp φ z w) := by
  rw [resolventRectangleIntegral_eq_clusterProjection hp φ z w hre him hc]
  exact periodicClusterProjection_idempotent hp φ _

/-- The range consists of all enclosed full generalized eigenspaces. -/
theorem range_resolventRectangleIntegral (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) :
    (resolventRectangleIntegral hp φ z w).range =
      periodicClusterSpace hp φ (rectanglePeriodicSpectrum hp φ z w) := by
  rw [resolventRectangleIntegral_eq_clusterProjection hp φ z w hre him hc]
  exact range_periodicClusterProjection hp φ _

/-- The rank of an admissible rectangular integral is its enclosed algebraic multiplicity. -/
theorem finrank_range_resolventRectangleIntegral (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) :
    Module.finrank ℂ (resolventRectangleIntegral hp φ z w).range =
      ∑ a ∈ rectanglePeriodicSpectrum hp φ z w, periodicAlgebraicMultiplicity hp φ a := by
  rw [resolventRectangleIntegral_eq_clusterProjection hp φ z w hre him hc]
  exact finrank_range_periodicClusterProjection hp φ _

/-- Ordered admissible rectangles selecting the same spectrum define the same whole operator. -/
theorem resolventRectangleIntegral_eq_of_spectrum_eq (hp : p ≠ ⊤) (φ : PairSpace p) (z w z' w' : ℂ)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hre' : z'.re ≤ w'.re) (him' : z'.im ≤ w'.im)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ)
    (hc' : RectangleIntegral.boundary z' w' ⊆ resolventSet hp φ)
    (hs : rectanglePeriodicSpectrum hp φ z w = rectanglePeriodicSpectrum hp φ z' w') :
    resolventRectangleIntegral hp φ z w = resolventRectangleIntegral hp φ z' w' := by
  rw [resolventRectangleIntegral_eq_clusterProjection hp φ z w hre him hc,
    resolventRectangleIntegral_eq_clusterProjection hp φ z' w' hre' him' hc', hs]

end NLS.ZakharovShabat
