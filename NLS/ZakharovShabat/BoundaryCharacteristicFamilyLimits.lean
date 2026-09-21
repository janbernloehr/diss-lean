import NLS.ZakharovShabat.BoundaryCharacteristicAnalytic
import NLS.ComplexAnalysis.AnalyticFamilyLimits
import NLS.ComplexAnalysis.UniformRootStability

/-!
# Spectral limits as the potential varies

Joint boundary characteristic analyticity implies locally uniform convergence
on the reflected-potential space. Zero-free boundaries preserve actual
boundary root counts near each fixed potential.
-/

noncomputable section
open Set Complex Filter Topology Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Varying the reflected potential gives locally uniform convergence of the boundary characteristic. -/
theorem tendstoLocallyUniformlyOn_boundaryCharacteristic_family (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : dirichletSubspace (p := p)) :
    TendstoLocallyUniformlyOn (fun ψ : dirichletSubspace (p := p) => b.characteristic hp ψ.val ψ.property)
      (b.characteristic hp φ.val φ.property) (𝓝 φ) univ := by
  have hc : Continuous (fun t : ℂ × dirichletSubspace (p := p) =>
      b.characteristic hp t.2.val t.2.property t.1) :=
    continuousOn_univ.mp (analyticOnNhd_boundaryCharacteristic_joint hp hp1 b).continuousOn
  have hswap : Continuous (fun t : dirichletSubspace (p := p) × ℂ => (t.2,t.1)) :=
    continuous_snd.prodMk continuous_fst
  have hs := hc.comp hswap
  exact tendstoLocallyUniformlyOn_of_joint_continuous
    (fun ψ : dirichletSubspace (p := p) => b.characteristic hp ψ.val ψ.property) hs φ

/-- Any compact set without boundary roots stays without boundary roots for nearby reflected potentials. -/
theorem eventually_boundaryCharacteristic_ne_zero_on_compact (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : dirichletSubspace (p := p)) {K : Set ℂ} (hK : IsCompact K)
    (hne : ∀ z ∈ K, b.characteristic hp φ.val φ.property z ≠ 0) :
    ∀ᶠ ψ : dirichletSubspace (p := p) in 𝓝 φ, ∀ z ∈ K, b.characteristic hp ψ.val ψ.property z ≠ 0 :=
  eventually_ne_zero_on_compact (tendstoLocallyUniformlyOn_boundaryCharacteristic_family hp hp1 b φ)
    hK ((b.analyticOnNhd_characteristic hp hp1 φ.val φ.property).continuousOn.mono (subset_univ _)) hne

/-- Every zero-free circle preserves its full boundary count on a potential neighborhood. -/
theorem eventually_boundaryCharacteristic_count_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : dirichletSubspace (p := p)) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hne : ∀ z ∈ sphere c r, b.characteristic hp φ.val φ.property z ≠ 0) :
    ∀ᶠ ψ : dirichletSubspace (p := p) in 𝓝 φ,
      analyticZeroCount (b.characteristic hp ψ.val ψ.property) (closedBall c r) =
        analyticZeroCount (b.characteristic hp φ.val φ.property) (closedBall c r) :=
  eventually_analyticZeroCount_eq (tendstoLocallyUniformlyOn_boundaryCharacteristic_family hp hp1 b φ)
    c r hr (fun ψ => (b.analyticOnNhd_characteristic hp hp1 ψ.val ψ.property).mono (subset_univ _))
    ((b.analyticOnNhd_characteristic hp hp1 φ.val φ.property).mono (subset_univ _)) hne

end NLS.ZakharovShabat
