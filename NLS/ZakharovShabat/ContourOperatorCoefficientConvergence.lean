import NLS.ZakharovShabat.ResolventCompactConvergence
import NLS.ZakharovShabat.SpectralReduction
import Mathlib.Topology.MetricSpace.Algebra

/-! # Bounded spectral restrictions under coefficient limits

The contour restriction `L P` equals the first weighted resolvent integral.
Consequently it converges in operator norm under bounded coefficientwise
convergence, although the unbounded operators themselves need not converge
in their domain-to-base operator norm.
-/
noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Applying the original operator to a resolvent is a bounded operation. -/
theorem operator_comp_resolventToDomain (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∈ resolventSet hp φ) :
    (operator hp φ).comp (resolventToDomain hp φ z) = z • resolvent hp φ z - 1 := by
  apply ContinuousLinearMap.ext
  intro f
  change operator hp φ (resolventToDomain hp φ z f) =
    z • domainInclusion (resolventToDomain hp φ z f) - f
  have h := spectralPencil_resolventToDomain hp φ z hz f
  rw [spectralPencil_apply] at h
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp h).symm)

/-- The bounded restriction of the operator is the first spectral moment of
its resolvent, integrated on the same contour as the projection. -/
theorem contourOperator_eq_weighted_resolvent_integral (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    contourOperator hp φ c r =
      (2*Real.pi*I : ℂ)⁻¹ • ∮ z in C(c,r), z • resolvent hp φ z := by
  let A := (ContinuousLinearMap.compL ℂ (PairSpace p) (Domain p) (PairSpace p)) (operator hp φ)
  change A ((2*Real.pi*I : ℂ)⁻¹ • ∮ z in C(c,r), resolventToDomain hp φ z) = _
  rw [map_smul, NLS.CircleIntegral.map A (circleIntegrable_resolventToDomain hp φ c r hr hc)]
  congr 1
  have he : (∮ z in C(c,r), A (resolventToDomain hp φ z)) =
      ∮ z in C(c,r), z • resolvent hp φ z - 1 := by
    apply circleIntegral.integral_congr hr
    intro z hz
    exact operator_comp_resolventToDomain hp φ z (hc hz)
  have hi : CircleIntegrable (fun z => z • resolvent hp φ z) c r :=
    (continuousOn_id.smul ((analyticOnNhd_resolvent hp φ).continuousOn.mono hc)).circleIntegrable hr
  have hi1 : CircleIntegrable (fun _ : ℂ => (1 : PairSpace p →L[ℂ] PairSpace p)) c r :=
    continuousOn_const.circleIntegrable hr
  rw [he, circleIntegral.integral_sub hi hi1]
  have hz : (∮ z in C(c,r), (1 : PairSpace p →L[ℂ] PairSpace p)) = 0 :=
    (DiffContOnCl.mk_ball (differentiable_const _).differentiableOn
      continuousOn_const).circleIntegral_eq_zero hr
  rw [hz, sub_zero]

/-- Every continuous scalar weight on a spectral-free circle preserves
operator-norm convergence of the resolvent integrals. -/
theorem tendsto_weighted_resolvent_integral_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → PairSpace p) (ψ : PairSpace p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp ψ)
    (g : ℂ → ℂ) (hg : ContinuousOn g (sphere c r)) :
    Tendsto (fun k => (2*Real.pi*I : ℂ)⁻¹ • ∮ z in C(c,r), g z • resolvent hp (φ k) z) l
      (𝓝 ((2*Real.pi*I : ℂ)⁻¹ • ∮ z in C(c,r), g z • resolvent hp ψ z)) := by
  have hloc := (tendstoLocallyUniformlyOn_resolvent_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂).mono hc
  have hg0 : TendstoUniformlyOn (fun _ : α => g) g l (sphere c r) := by
    intro U hU
    exact Eventually.of_forall fun _ _ _ => refl_mem_uniformity hU
  have hweight := hg0.tendstoLocallyUniformlyOn.smul₀ hloc hg
    ((analyticOnNhd_resolvent hp ψ).continuousOn.mono hc)
  have hunif := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere c r)).mp hweight
  have hev := eventually_compact_subset_resolventSet_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂
    (sphere c r) (isCompact_sphere c r) hc
  have hcont : ∀ᶠ k in l, ContinuousOn (fun z => g z • resolvent hp (φ k) z) (sphere c r) :=
    hev.mono fun k hk => hg.smul ((analyticOnNhd_resolvent hp (φ k)).continuousOn.mono hk)
  exact (hunif.tendsto_circleIntegral_of_continuousOn hr hcont).const_smul (2*Real.pi*I : ℂ)⁻¹

/-- Bounded coefficient limits give norm convergence of the bounded
restrictions of the original unbounded operator to its contour subspaces. -/
theorem tendsto_contourOperator_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → PairSpace p) (ψ : PairSpace p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp ψ) :
    Tendsto (fun k => contourOperator hp (φ k) c r) l (𝓝 (contourOperator hp ψ c r)) := by
  rw [contourOperator_eq_weighted_resolvent_integral hp ψ c r hr hc]
  apply (tendsto_weighted_resolvent_integral_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂
    c r hr hc id continuousOn_id).congr'
  filter_upwards [eventually_compact_subset_resolventSet_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂
    (sphere c r) (isCompact_sphere c r) hc] with k hk
  exact (contourOperator_eq_weighted_resolvent_integral hp (φ k) c r hr hk).symm

end NLS.ZakharovShabat
