import NLS.ComplexAnalysis.ClosedUpperExtension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! # Matching boundary limits and an analytic target coordinate

Matching upper, lower and real-axis values give continuity. A locally
invertible analytic target coordinate then recovers analyticity of the
original map from that of its composition.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem continuousAt_realBoundaryExtension_of_limits (F : ℂ → ℂ) (B : ℝ → ℂ) (x : ℝ)
    (hB : ContinuousAt B x)
    (hu : Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (B x)))
    (hl : Tendsto F (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (B x))) :
    ContinuousAt (realBoundaryExtension F B) (x : ℂ) := by
  have hupper : Tendsto (realBoundaryExtension F B)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (B x)) := by
    apply hu.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (if_neg hz.ne').symm
  have hlower : Tendsto (realBoundaryExtension F B)
      (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (B x)) := by
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (if_neg hz.ne).symm
  have hreal : Tendsto (realBoundaryExtension F B)
      (𝓝[{z : ℂ | z.im = 0}] (x : ℂ)) (𝓝 (B x)) := by
    have ht := hB.tendsto.comp
      (continuous_re.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[{z : ℂ | z.im = 0}] (x : ℂ) ≤ 𝓝 (x : ℂ)))
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (if_pos hz).symm
  have hcover : ({z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im < 0}) ∪ {z : ℂ | z.im = 0} = univ := by
    ext z
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
    rcases lt_trichotomy 0 z.im with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h.symm
    · exact Or.inl (Or.inr h)
  have ht := tendsto_sup.mpr ⟨tendsto_sup.mpr ⟨hupper, hlower⟩, hreal⟩
  rw [← nhdsWithin_union, ← nhdsWithin_union, hcover, nhdsWithin_univ] at ht
  simpa [ContinuousAt, realBoundaryExtension] using ht

theorem analyticAt_of_continuousAt_coordinate (φ H : ℂ → ℂ) (z : ℂ)
    (hφ : AnalyticAt ℂ φ (H z)) (hne : deriv φ (H z) ≠ 0)
    (hH : ContinuousAt H z) (hc : AnalyticAt ℂ (φ ∘ H) z) : AnalyticAt ℂ H z := by
  let r := hφ.hasStrictDerivAt.localInverse _ _ _ hne
  have hra : AnalyticAt ℂ r (φ (H z)) := hφ.analyticAt_localInverse hne
  have he : ∀ᶠ w in 𝓝 (H z), r (φ w) = w :=
    hφ.hasStrictDerivAt.eventually_left_inverse hne
  exact (hra.comp (f := φ ∘ H) hc).congr (hH.tendsto.eventually he)

end NLS.ComplexAnalysis
