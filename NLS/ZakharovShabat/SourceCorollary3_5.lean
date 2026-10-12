import NLS.ZakharovShabat.SourceResolvent
import NLS.ZakharovShabat.SpectralLocalization

/-! # Corollary 3.5 in the original source topology

One open convex neighborhood contains the potential and zero. Every
larger cutoff gives a compact analytic original-norm resolvent throughout
the exact box-and-disk complement printed in the source. The vertical
box boundary is excluded from the box; the horizontal boundary is included.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One source neighborhood and positive cutoff control both high imaginary
parts (including equality) and all distant punctured strips. -/
theorem exists_source_uniform_height_and_strips (hp : p ≠ ⊤) (φ : CoeffPair p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p), 0 < N ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U,
        (∀ z : ℂ, (N : ℝ) ≤ |z.im| → z ∈ sourceResolventSet hp ψ) ∧
        (∀ n : ℤ, N ≤ n.natAbs → verticalStrip n r ⊆ sourceResolventSet hp ψ) := by
  obtain ⟨N,V,hN,ho,hc,hφ,h0,hbounds⟩ :=
    exists_uniform_height_and_strips hp (CoeffPair.toMax p φ) hr hrπ
  refine ⟨N,(CoeffPair.toMax p) ⁻¹' V,hN,ho.preimage (CoeffPair.toMax p).continuous,
    hc.linear_preimage ((CoeffPair.toMax p).toContinuousLinearMap.restrictScalars ℝ).toLinearMap,
    hφ,?_,?_⟩
  · simpa only [Set.mem_preimage,map_zero] using h0
  · intro ψ hψ
    simpa only [sourceResolventSet_eq] using hbounds (CoeffPair.toMax p ψ) hψ

/-- Corollary 3.5, strengthened to all larger cutoffs on the same original-norm
neighborhood. The neighborhood is convex and contains zero. -/
theorem sourceCorollary3_5_all_larger (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧
      φ ∈ U ∧ 0 ∈ U ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ψ ∈ U,
        spectralExterior N (Real.pi/4) ⊆ sourceResolventSet hp ψ ∧
        AnalyticOnNhd ℂ (sourceResolvent hp ψ) (spectralExterior N (Real.pi/4)) ∧
        (∀ z ∈ spectralExterior N (Real.pi/4), IsCompactOperator (sourceResolvent hp ψ z)) ∧
        (sourceResolventSet hp ψ)ᶜ ⊆ centralSpectralBox N ∪ highSpectralDisks N (Real.pi/4) := by
  obtain ⟨N₀,U,hN₀,ho,hc,hφ,h0,hbounds⟩ :=
    exists_source_uniform_height_and_strips hp φ (r := Real.pi/4) (by positivity) le_rfl
  refine ⟨N₀,U,hN₀,ho,hc,⟨⟨0,h0⟩,hc.isPreconnected⟩,hφ,h0,?_⟩
  intro N hN ψ hψ
  have he : spectralExterior N (Real.pi/4) ⊆ sourceResolventSet hp ψ := by
    intro z hz
    rcases spectralExterior_height_or_strip N le_rfl hz with hi | ⟨n,hn,hs⟩
    · exact (hbounds ψ hψ).1 z ((by exact_mod_cast hN : (N₀ : ℝ) ≤ (N : ℝ)).trans hi.le)
    · exact (hbounds ψ hψ).2 n (hN.trans hn) hs
  refine ⟨he,(analyticOnNhd_sourceResolvent hp ψ).mono he,
    fun z _ => isCompactOperator_sourceResolvent hp ψ z,?_⟩
  intro z hz
  by_contra hout
  exact hz (he hout)

/-- The printed one-cutoff statement, including the actual spectrum enclosure. -/
theorem sourceCorollary3_5 (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p), 0 < N ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧
      φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        spectralExterior N (Real.pi/4) ⊆ sourceResolventSet hp ψ ∧
        AnalyticOnNhd ℂ (sourceResolvent hp ψ) (spectralExterior N (Real.pi/4)) ∧
        (∀ z ∈ spectralExterior N (Real.pi/4), IsCompactOperator (sourceResolvent hp ψ z)) ∧
        (sourceResolventSet hp ψ)ᶜ ⊆ centralSpectralBox N ∪ highSpectralDisks N (Real.pi/4) := by
  obtain ⟨N,U,hN,ho,hc,hconn,hφ,h0,h⟩ := sourceCorollary3_5_all_larger hp φ
  exact ⟨N,U,hN,ho,hc,hconn,hφ,h0,h N le_rfl⟩

end NLS.ZakharovShabat
