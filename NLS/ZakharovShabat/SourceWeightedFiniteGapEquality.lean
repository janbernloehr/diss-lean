import NLS.ZakharovShabat.SourceWeightedFiniteGapDensity

/-! # Equality from physical finite-gap approximation in the native weighted norm -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Two continuous scalar functions on the full native weighted real source
agree if they agree on its actual spectral finite-gap sources. -/
theorem eq_of_continuous_weighted_finiteGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (f g : weightedRealSourceSubmodule (p := p) w → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hfinite : ∀ a : weightedRealSourceSubmodule (p := p) w,
      originalWeightedRealSource w a ∈ sourceFiniteGapLocus hp hp1 → f a = g a)
    (a : weightedRealSourceSubmodule (p := p) w) : f a = g a := by
  choose b hb hclose using fun j : ℕ => exists_weightedRealSource_finiteGap_norm_sub_lt
    hp hp1 w a (1/((j:ℝ)+1)) (by positivity)
  have hlim : Tendsto b atTop (𝓝 a) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun j => norm_nonneg (b j-a)) (fun j => (hclose j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hflim : Tendsto (fun j => f (b j)) atTop (𝓝 (f a)) := (hf.tendsto a).comp hlim
  have hglim : Tendsto (fun j => g (b j)) atTop (𝓝 (g a)) := (hg.tendsto a).comp hlim
  have heq : (fun j => f (b j)) = fun j => g (b j) := funext fun j => hfinite (b j) (hb j)
  rw [heq] at hflim
  exact tendsto_nhds_unique hflim hglim

end NLS.ZakharovShabat
