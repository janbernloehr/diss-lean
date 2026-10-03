import NLS.FunctionalAnalysis.BoundedSegmentLimits
import NLS.ZakharovShabat.SourceSpectralCoefficientConvergence

/-! # Common resolvent sets along interpolation segments

A compact subset of the limit source's resolvent set is eventually spectral-free
on every point of the full segment from the limit source to each approximant.
Only bounded coefficientwise convergence is required.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Compact resolvent subsets persist uniformly along all interpolation segments. -/
theorem eventually_compact_subset_source_segment_resolventSet
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n)))
    (K : Set ℂ) (hK : IsCompact K) (hKs : K ⊆ resolventSet hp (periodOnePotential ψ)) :
    ∀ᶠ k in l, ∀ t ∈ Icc (0 : ℝ) 1,
      K ⊆ resolventSet hp (periodOnePotential (BoundedSegmentLimits.segment ψ (φ k) t)) := by
  let a : α × Icc (0 : ℝ) 1 → CoeffPair p := fun t => BoundedSegmentLimits.segment ψ (φ t.1) t.2
  have ha := BoundedSegmentLimits.bounded_range_segment φ ψ hb
  have h₁ (n : ℤ) : Tendsto (fun t => (a t).fst n) (l ×ˢ ⊤) (𝓝 (ψ.fst n)) := by
    let F : CoeffPair p →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp
      ((ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).comp (CoeffPair.toMax p).toContinuousLinearMap)
    exact BoundedSegmentLimits.tendsto_coordinate_segment φ ψ F.toLinearMap (ht₁ n)
  have h₂ (n : ℤ) : Tendsto (fun t => (a t).snd n) (l ×ˢ ⊤) (𝓝 (ψ.snd n)) := by
    let F : CoeffPair p →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp
      ((ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).comp (CoeffPair.toMax p).toContinuousLinearMap)
    exact BoundedSegmentLimits.tendsto_coordinate_segment φ ψ F.toLinearMap (ht₂ n)
  have h := eventually_compact_subset_source_resolventSet_of_bounded_coefficientwise hp hp1 a ψ ha h₁ h₂ K hK hKs
  rw [← principal_univ, eventually_prod_principal_iff] at h
  filter_upwards [h] with k hk t ht
  exact hk ⟨t,ht⟩ (mem_univ _)

end NLS.ZakharovShabat
