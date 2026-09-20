import NLS.ZakharovShabat.CanonicalCriticalPoints
import NLS.ComplexAnalysis.AnalyticFamilyLimits
import NLS.ComplexAnalysis.UniformRootStability

/-!
# Spectral limits as the potential varies

Joint discriminant analyticity implies locally uniform convergence of the
trace and its derivative on the even-potential space. Zero-free boundaries
therefore preserve critical-point counts near each fixed potential.
-/

noncomputable section
open Set Complex Filter Topology Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Varying the even potential gives locally uniform convergence of the discriminant. -/
theorem tendstoLocallyUniformlyOn_discriminant_family (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) :
    TendstoLocallyUniformlyOn (fun ψ : pairParitySubspace (p := p) 0 => canonicalDiscriminant hp ψ.val)
      (canonicalDiscriminant hp φ.val) (𝓝 φ) univ := by
  have hc : Continuous (fun t : ℂ × pairParitySubspace (p := p) 0 =>
      canonicalDiscriminant hp t.2.val t.1) :=
    continuousOn_univ.mp (analyticOnNhd_canonicalDiscriminant_joint hp hp1).continuousOn
  have hswap : Continuous (fun t : pairParitySubspace (p := p) 0 × ℂ => (t.2,t.1)) :=
    continuous_snd.prodMk continuous_fst
  have hs := hc.comp hswap
  exact tendstoLocallyUniformlyOn_of_joint_continuous
    (fun ψ : pairParitySubspace (p := p) 0 => canonicalDiscriminant hp ψ.val) hs φ

/-- The spectral derivative has the same locally uniform dependence on even potentials. -/
theorem tendstoLocallyUniformlyOn_discriminant_derivative_family (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) :
    TendstoLocallyUniformlyOn (fun ψ : pairParitySubspace (p := p) 0 => deriv (canonicalDiscriminant hp ψ.val))
      (deriv (canonicalDiscriminant hp φ.val)) (𝓝 φ) univ :=
  (tendstoLocallyUniformlyOn_discriminant_family hp hp1 φ).deriv
    (Eventually.of_forall (fun ψ => (analyticOnNhd_canonicalDiscriminant hp hp1 ψ.val ψ.property).differentiableOn))
    isOpen_univ

/-- Any compact set without critical points stays without critical points for nearby even potentials. -/
theorem eventually_discriminant_derivative_ne_zero_on_compact (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) {K : Set ℂ} (hK : IsCompact K)
    (hne : ∀ z ∈ K, deriv (canonicalDiscriminant hp φ.val) z ≠ 0) :
    ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ, ∀ z ∈ K, deriv (canonicalDiscriminant hp ψ.val) z ≠ 0 :=
  eventually_ne_zero_on_compact (tendstoLocallyUniformlyOn_discriminant_derivative_family hp hp1 φ)
    hK ((analyticOnNhd_discriminant_derivative hp hp1 φ.val φ.property).continuousOn.mono (subset_univ _)) hne

/-- Every zero-free circle preserves its full critical count on a potential neighborhood. -/
theorem eventually_discriminant_critical_count_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hne : ∀ z ∈ sphere c r, deriv (canonicalDiscriminant hp φ.val) z ≠ 0) :
    ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ,
      analyticZeroCount (deriv (canonicalDiscriminant hp ψ.val)) (closedBall c r) =
        analyticZeroCount (deriv (canonicalDiscriminant hp φ.val)) (closedBall c r) :=
  eventually_analyticZeroCount_eq (tendstoLocallyUniformlyOn_discriminant_derivative_family hp hp1 φ)
    c r hr (fun ψ => (analyticOnNhd_discriminant_derivative hp hp1 ψ.val ψ.property).mono (subset_univ _))
    ((analyticOnNhd_discriminant_derivative hp hp1 φ.val φ.property).mono (subset_univ _)) hne

end NLS.ZakharovShabat
