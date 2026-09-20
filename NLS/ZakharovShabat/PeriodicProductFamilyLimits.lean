import NLS.ZakharovShabat.CanonicalPeriodicProductAnalytic
import NLS.ComplexAnalysis.AnalyticFamilyLimits
import NLS.ComplexAnalysis.UniformRootStability

/-!
# Periodic root stability as the potential varies

Joint analyticity of the canonical periodic product gives locally uniform
parameter limits and stable circular counts with original multiplicities.
These statements hold on the full potential space, without a parity assumption.
-/

noncomputable section
open Set Complex Filter Topology Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The periodic product converges locally uniformly as the potential varies. -/
theorem tendstoLocallyUniformlyOn_periodicProduct_family (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) :
    TendstoLocallyUniformlyOn (fun ψ : PairSpace p => canonicalPeriodicProduct hp ψ)
      (canonicalPeriodicProduct hp φ) (𝓝 φ) univ := by
  have hc : Continuous (fun t : ℂ × PairSpace p => canonicalPeriodicProduct hp t.2 t.1) :=
    continuousOn_univ.mp (analyticOnNhd_canonicalPeriodicProduct_joint hp hp1).continuousOn
  have hswap : Continuous (fun t : PairSpace p × ℂ => (t.2,t.1)) :=
    continuous_snd.prodMk continuous_fst
  have hs := hc.comp hswap
  exact tendstoLocallyUniformlyOn_of_joint_continuous _ hs φ

/-- Compact spectral-free sets stay spectral-free on a neighborhood of the potential. -/
theorem eventually_periodicSpectrum_avoids_compact (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) {K : Set ℂ} (hK : IsCompact K)
    (hne : ∀ z ∈ K, z ∉ periodicSpectrum hp φ) :
    ∀ᶠ ψ : PairSpace p in 𝓝 φ, ∀ z ∈ K, z ∉ periodicSpectrum hp ψ := by
  have he := eventually_ne_zero_on_compact (tendstoLocallyUniformlyOn_periodicProduct_family hp hp1 φ)
    hK ((analyticOnNhd_canonicalPeriodicProduct hp hp1 φ).continuousOn.mono (subset_univ _))
    (fun z hz => fun hzero => hne z hz ((canonicalPeriodicProduct_eq_zero_iff hp hp1 φ z).mp hzero))
  filter_upwards [he] with ψ hψ z hz hspec
  exact hψ z hz ((canonicalPeriodicProduct_eq_zero_iff hp hp1 ψ z).mpr hspec)

/-- Each spectral-free circle preserves its periodic analytic count near the potential. -/
theorem eventually_periodicProduct_count_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hne : ∀ z ∈ sphere c r, z ∉ periodicSpectrum hp φ) :
    ∀ᶠ ψ : PairSpace p in 𝓝 φ,
      analyticZeroCount (canonicalPeriodicProduct hp ψ) (closedBall c r) =
        analyticZeroCount (canonicalPeriodicProduct hp φ) (closedBall c r) :=
  eventually_analyticZeroCount_eq (tendstoLocallyUniformlyOn_periodicProduct_family hp hp1 φ)
    c r hr (fun ψ => (analyticOnNhd_canonicalPeriodicProduct hp hp1 ψ).mono (subset_univ _))
    ((analyticOnNhd_canonicalPeriodicProduct hp hp1 φ).mono (subset_univ _))
    (fun z hz hzero => hne z hz ((canonicalPeriodicProduct_eq_zero_iff hp hp1 φ z).mp hzero))

/-- On a compact set, nearby periodic roots remain in any open neighborhood of the original roots. -/
theorem eventually_periodicSpectrum_mem_open (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hroots : ∀ z ∈ K, z ∈ periodicSpectrum hp φ → z ∈ U) :
    ∀ᶠ ψ : PairSpace p in 𝓝 φ, ∀ z ∈ K, z ∈ periodicSpectrum hp ψ → z ∈ U := by
  have he := eventually_roots_mem_open (tendstoLocallyUniformlyOn_periodicProduct_family hp hp1 φ)
    hK hU ((analyticOnNhd_canonicalPeriodicProduct hp hp1 φ).continuousOn.mono (subset_univ _))
    (fun z hz hzero => hroots z hz ((canonicalPeriodicProduct_eq_zero_iff hp hp1 φ z).mp hzero))
  filter_upwards [he] with ψ hψ z hz hspec
  exact hψ z hz ((canonicalPeriodicProduct_eq_zero_iff hp hp1 ψ z).mpr hspec)

end NLS.ZakharovShabat
