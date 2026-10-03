import NLS.ZakharovShabat.SpectralClusterCoefficientStability

/-! # Spectral convergence in period-one source coordinates

The period-doubling map preserves bounded coefficient limits. These wrappers
apply compact resolvent convergence and spectral cluster stability directly
to the dissertation's source pairs, for every finite exponent greater than one.
-/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem bounded_periodOnePotential_range {α : Type*}
    (φ : α → CoeffPair p) (hb : Bornology.IsBounded (range φ)) :
    Bornology.IsBounded (range (fun k => periodOnePotential (φ k))) := by
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact (norm_periodOnePotential_le (φ k)).trans (hM _ ⟨k, rfl⟩)

/-- Locally uniform norm-resolvent convergence for bounded source coefficient limits. -/
theorem tendstoLocallyUniformlyOn_source_resolvent_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n))) :
    TendstoLocallyUniformlyOn (fun k z => resolvent hp (periodOnePotential (φ k)) z) (resolvent hp (periodOnePotential ψ)) l
      (resolventSet hp (periodOnePotential ψ)) := by
  exact tendstoLocallyUniformlyOn_resolvent_of_bounded_coefficientwise hp hp1
    (fun k => periodOnePotential (φ k)) (periodOnePotential ψ)
    (bounded_periodOnePotential_range φ hb)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).fst) ψ.fst ht₁)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).snd) ψ.snd ht₂)

/-- Compact subsets of the limit source resolvent set are eventually common to the family. -/
theorem eventually_compact_subset_source_resolventSet_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n)))
    (K : Set ℂ) (hK : IsCompact K) (hKs : K ⊆ resolventSet hp (periodOnePotential ψ)) :
    ∀ᶠ k in l, K ⊆ resolventSet hp (periodOnePotential (φ k)) := by
  exact eventually_compact_subset_resolventSet_of_bounded_coefficientwise hp hp1
    (fun k => periodOnePotential (φ k)) (periodOnePotential ψ)
    (bounded_periodOnePotential_range φ hb)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).fst) ψ.fst ht₁)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).snd) ψ.snd ht₂) K hK hKs

/-- Norm convergence of source contour projections along bounded coefficient limits. -/
theorem tendsto_source_resolventCircleIntegral_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp (periodOnePotential ψ)) :
    Tendsto (fun k => resolventCircleIntegral hp (periodOnePotential (φ k)) c r) l
      (𝓝 (resolventCircleIntegral hp (periodOnePotential ψ) c r)) := by
  exact tendsto_resolventCircleIntegral_of_bounded_coefficientwise hp hp1
    (fun k => periodOnePotential (φ k)) (periodOnePotential ψ)
    (bounded_periodOnePotential_range φ hb)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).fst) ψ.fst ht₁)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).snd) ψ.snd ht₂) c r hr hc

/-- Eventual stability of source contour projection ranks and circle membership. -/
theorem eventually_finrank_source_resolventCircleIntegral_eq_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp (periodOnePotential ψ)) :
    ∀ᶠ k in l, sphere c r ⊆ resolventSet hp (periodOnePotential (φ k)) ∧
      Module.finrank ℂ (resolventCircleIntegral hp (periodOnePotential (φ k)) c r).range =
        Module.finrank ℂ (resolventCircleIntegral hp (periodOnePotential ψ) c r).range := by
  exact eventually_finrank_resolventCircleIntegral_eq_of_bounded_coefficientwise hp hp1
    (fun k => periodOnePotential (φ k)) (periodOnePotential ψ)
    (bounded_periodOnePotential_range φ hb)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).fst) ψ.fst ht₁)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).snd) ψ.snd ht₂) c r hr hc

/-- Eventual equality of total enclosed source algebraic multiplicities. -/
theorem eventually_sum_source_enclosed_multiplicity_eq_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp (periodOnePotential ψ)) :
    ∀ᶠ k in l,
      ∑ z ∈ enclosedPeriodicSpectrum hp (periodOnePotential (φ k)) c r, periodicAlgebraicMultiplicity hp (periodOnePotential (φ k)) z =
        ∑ z ∈ enclosedPeriodicSpectrum hp (periodOnePotential ψ) c r, periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z := by
  exact eventually_sum_enclosed_multiplicity_eq_of_bounded_coefficientwise hp hp1
    (fun k => periodOnePotential (φ k)) (periodOnePotential ψ)
    (bounded_periodOnePotential_range φ hb)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).fst) ψ.fst ht₁)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).snd) ψ.snd ht₂) c r hr hc

end NLS.ZakharovShabat
