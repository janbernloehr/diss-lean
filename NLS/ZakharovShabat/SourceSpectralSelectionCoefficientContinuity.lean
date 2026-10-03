import NLS.ZakharovShabat.SourceSegmentResolventPersistence
import NLS.ZakharovShabat.SourceRealTypeConvex
import NLS.ZakharovShabat.EntirePeriodicProductOrders

/-! # Bounded coefficient continuity of continuous real-source spectral selections

A continuous eigenvalue selection cannot cross a spectral-free circle along
a real source segment. Uniform resolvent persistence along these segments
therefore upgrades strong continuity of the selection to continuity along
bounded coefficientwise limits. No common cluster labeling is assumed.
-/
noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Straight real interpolation preserves the Fourier real-type relation. -/
theorem isRealType_source_segment (φ ψ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (hψ : IsRealType (CoeffPair.toMax p ψ)) (t : ℝ) :
    IsRealType (CoeffPair.toMax p (BoundedSegmentLimits.segment ψ φ t)) := by
  intro n
  change ψ.snd n + (t : ℂ)*(φ.snd n-ψ.snd n) =
    conj (ψ.fst (-n) + (t : ℂ)*(φ.fst (-n)-ψ.fst (-n)))
  have ha : φ.snd n = conj (φ.fst (-n)) := hφ n
  have hb : ψ.snd n = conj (ψ.fst (-n)) := hψ n
  rw [map_add, map_mul, map_sub, Complex.conj_ofReal, ← ha, ← hb]

/-- Any spectral selection continuous on real sources is continuous under
bounded coefficientwise limits of real sources. The argument keeps each
label on its own interpolation segment and allows coincident eigenvalues. -/
theorem tendsto_source_spectral_selection_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax p (φ k))) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n)))
    (f : CoeffPair p → ℂ)
    (hf : ∀ χ, IsRealType (CoeffPair.toMax p χ) → ContinuousAt f χ)
    (hspec : ∀ χ, IsRealType (CoeffPair.toMax p χ) → f χ ∈ periodicSpectrum hp (periodOnePotential χ)) :
    Tendsto (fun k => f (φ k)) l (𝓝 (f ψ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R,hR,hiso⟩ := exists_periodicSpectrum_isolating_closedBall hp (periodOnePotential ψ) (f ψ)
  let r := min R ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r ≤ R := by dsimp [r]; linarith [min_le_left R ε]
  have hrε : r ≤ ε := by dsimp [r]; linarith [min_le_right R ε]
  have hc : sphere (f ψ) r ⊆ resolventSet hp (periodOnePotential ψ) := by
    intro z hz
    by_contra hn
    have he := hiso z ((closedBall_subset_closedBall hrR) (sphere_subset_closedBall hz)) hn
    subst z
    have hz0 : 0 = r := by simpa only [mem_sphere, dist_self] using hz
    exact hr.ne' hz0.symm
  have hev := eventually_compact_subset_source_segment_resolventSet hp hp1 φ ψ hb ht₁ ht₂
    (sphere (f ψ) r) (isCompact_sphere _ _) hc
  filter_upwards [hev] with k hk
  have hreal (t : ℝ) := isRealType_source_segment (φ k) ψ (hφ k) hψ t
  have hcont : Continuous (fun t : ℝ => f (BoundedSegmentLimits.segment ψ (φ k) t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hf _ (hreal t)).comp (BoundedSegmentLimits.continuous_segment ψ (φ k)).continuousAt
  have hne : ∀ t ∈ Icc (0 : ℝ) 1,
      dist (f (BoundedSegmentLimits.segment ψ (φ k) t)) (f ψ) ≠ r := by
    intro t ht he
    exact hspec _ (hreal t) (hk t ht (show f (BoundedSegmentLimits.segment ψ (φ k) t) ∈ sphere (f ψ) r from he))
  have hlt := isPreconnected_Icc.gt_of_ne (hcont.dist continuous_const).continuousOn hne
    (show ∃ t ∈ Icc (0 : ℝ) 1, dist (f (BoundedSegmentLimits.segment ψ (φ k) t)) (f ψ) < r from
      ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa using hr⟩)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
  exact (show dist (f (φ k)) (f ψ) < r by simpa using hlt).trans_le hrε

end NLS.ZakharovShabat
