import NLS.ZakharovShabat.ContourOperatorCoefficientConvergence
import NLS.ZakharovShabat.ContourTrace

/-! # Spectral trace convergence under bounded coefficient limits

Projection transport puts the varying spectral restriction on the fixed
finite-dimensional limit range. Its norm convergence proves convergence of
every intrinsic power trace, and hence of the midpoint and squared-gap
expressions used for rank-two spectral clusters.
-/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Projection transport tends to the identity under bounded coefficient limits. -/
theorem tendsto_contourTransport_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → PairSpace p) (ψ : PairSpace p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp ψ) :
    Tendsto (fun k => contourTransport hp ψ (φ k) c r) l (𝓝 1) := by
  have ht := tendsto_resolventCircleIntegral_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂ c r hr hc
  have h := (ht.mul_const (resolventCircleIntegral hp ψ c r)).add
    ((ht.const_sub 1).mul_const (1-resolventCircleIntegral hp ψ c r))
  change Tendsto (fun k => contourTransport hp ψ (φ k) c r) l
    (𝓝 (contourTransport hp ψ ψ c r)) at h
  simpa only [contourTransport_self hp ψ c r hr hc] using h

/-- The actual spectral restrictions converge on one fixed finite-dimensional
range, using the explicitly constructed projection transport. -/
theorem tendsto_reducedContourOperator_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → PairSpace p) (ψ : PairSpace p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp ψ) :
    Tendsto (fun k => reducedContourOperator hp ψ (φ k) c r) l
      (𝓝 (reducedContourOperator hp ψ ψ c r)) := by
  have hT : Tendsto (fun k => contourTransport hp ψ (φ k) c r) l
      (𝓝 (contourTransport hp ψ ψ c r)) := by
    rw [contourTransport_self hp ψ c r hr hc]
    exact tendsto_contourTransport_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂ c r hr hc
  have hA := tendsto_contourOperator_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂ c r hr hc
  have hu : IsUnit (contourTransport hp ψ ψ c r) := by
    rw [contourTransport_self hp ψ c r hr hc]
    exact isUnit_one
  have hinv := (analyticOnNhd_inverse (𝕜 := ℂ) _ hu).continuousAt.tendsto.comp hT
  have hB := (hinv.mul hA).mul hT
  exact (ProjectionTransport.compressionMap (resolventCircleIntegral hp ψ c r)).continuous.continuousAt.tendsto.comp hB

/-- Every intrinsic spectral power trace converges under bounded coefficient
limits; trace is taken only after transport to the finite-dimensional limit range. -/
theorem tendsto_contourTracePower_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → PairSpace p) (ψ : PairSpace p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp ψ) (m : ℕ) :
    Tendsto (fun k => contourTracePower hp (φ k) c r m) l
      (𝓝 (contourTracePower hp ψ c r m)) := by
  let : FiniteDimensional ℂ (resolventCircleIntegral hp ψ c r).range :=
    finiteDimensional_range_resolventCircleIntegral hp ψ c r hr hc
  have hA := tendsto_reducedContourOperator_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂ c r hr hc
  let : NormedRing ((resolventCircleIntegral hp ψ c r).range →L[ℂ]
      (resolventCircleIntegral hp ψ c r).range) := inferInstance
  have hpow : Tendsto (fun k => reducedContourOperator hp ψ (φ k) c r ^ m) l
      (𝓝 (reducedContourOperator hp ψ ψ c r ^ m)) := hA.pow m
  have ht := (FiniteSpectralTrace.traceCLM (resolventCircleIntegral hp ψ c r).range).continuous.continuousAt.tendsto.comp hpow
  have hunit : ∀ᶠ k in l, IsUnit (contourTransport hp ψ (φ k) c r) :=
    (tendsto_contourTransport_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂ c r hr hc).eventually
      (Units.isOpen.mem_nhds isUnit_one)
  have hcircle := eventually_compact_subset_resolventSet_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂
    (sphere c r) (isCompact_sphere c r) hc
  have ht' : Tendsto (fun k => LinearMap.trace ℂ (resolventCircleIntegral hp ψ c r).range
      ((reducedContourOperator hp ψ (φ k) c r).toLinearMap ^ m)) l
      (𝓝 (contourTracePower hp ψ c r m)) := by
    simpa only [Function.comp_def, FiniteSpectralTrace.traceCLM_apply,
      ContinuousLinearMap.toLinearMap_pow, contourTracePower] using ht
  apply ht'.congr'
  filter_upwards [hunit, hcircle] with k hk hkc
  exact (contourTracePower_eq_reduced hp ψ (φ k) c r hr hc hkc hk m).symm

/-- Both symmetric rank-two trace expressions converge, even at a repeated eigenvalue. -/
theorem tendsto_contourMidpoint_and_squaredGap_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → PairSpace p) (ψ : PairSpace p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp ψ) :
    Tendsto (fun k => contourMidpoint hp (φ k) c r) l (𝓝 (contourMidpoint hp ψ c r)) ∧
      Tendsto (fun k => contourSquaredGap hp (φ k) c r) l (𝓝 (contourSquaredGap hp ψ c r)) := by
  have h₁ := tendsto_contourTracePower_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂ c r hr hc 1
  have h₂ := tendsto_contourTracePower_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂ c r hr hc 2
  exact ⟨h₁.div_const 2, (h₂.const_mul 2).sub (h₁.pow 2)⟩

end NLS.ZakharovShabat
