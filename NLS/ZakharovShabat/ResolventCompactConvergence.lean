import NLS.ZakharovShabat.ResolventReferenceChange
import NLS.ZakharovShabat.NeumannResolventCoefficientContinuity
import NLS.ZakharovShabat.ResolventContour
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! # Compact spectral convergence of resolvents and contour operators

Convergence at one common resolvent parameter propagates locally uniformly
through the limit resolvent set. Compact subsets are eventually common
resolvent subsets. Bounded coefficient limits supply the reference parameter.
-/
noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One reference-point limit gives locally uniform operator-norm convergence
throughout the limit's resolvent set. -/
theorem tendstoLocallyUniformlyOn_resolvent_of_reference
    (hp : p ≠ ⊤) {α : Type*} {l : Filter α} (φ : α → PairSpace p) (ψ : PairSpace p)
    (z : ℂ) (hzφ : ∀ k, z ∈ resolventSet hp (φ k)) (hzψ : z ∈ resolventSet hp ψ)
    (ht : Tendsto (fun k => resolvent hp (φ k) z) l (𝓝 (resolvent hp ψ z))) :
    TendstoLocallyUniformlyOn (fun k w => resolvent hp (φ k) w) (resolvent hp ψ) l
      (resolventSet hp ψ) := by
  apply (isOpen_resolventSet hp ψ).tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro w hw
  have hvar := (eventually_mem_and_tendsto_resolvent_of_reference_and_parameter hp
    (fun t : α × ℂ => φ t.1) ψ z (fun t => hzφ t.1) hzψ
    (ht.comp tendsto_fst) Prod.snd w tendsto_snd hw).2
  have hlim := ((analyticOnNhd_resolvent hp ψ w hw).continuousAt.tendsto).comp
    (tendsto_snd : Tendsto (fun t : α × ℂ => t.2) (l ×ˢ 𝓝 w) (𝓝 w))
  exact (hlim.prodMk_nhds hvar).mono_right (nhds_le_uniformity _)

/-- Every compact subset of the limit resolvent set is eventually a common
resolvent subset, with one index bound for all its spectral parameters. -/
theorem eventually_compact_subset_resolventSet_of_reference
    (hp : p ≠ ⊤) {α : Type*} {l : Filter α} (φ : α → PairSpace p) (ψ : PairSpace p)
    (z : ℂ) (hzφ : ∀ k, z ∈ resolventSet hp (φ k)) (hzψ : z ∈ resolventSet hp ψ)
    (ht : Tendsto (fun k => resolvent hp (φ k) z) l (𝓝 (resolvent hp ψ z)))
    (K : Set ℂ) (hK : IsCompact K) (hKs : K ⊆ resolventSet hp ψ) :
    ∀ᶠ k in l, K ⊆ resolventSet hp (φ k) := by
  have hc : Continuous (fun t : (PairSpace p →L[ℂ] PairSpace p) × ℂ =>
      (1 : PairSpace p →L[ℂ] PairSpace p) + (t.2-z) • t.1) := by fun_prop
  have he : ∀ᶠ A : PairSpace p →L[ℂ] PairSpace p in 𝓝 (resolvent hp ψ z),
      ∀ w ∈ K, IsUnit (1+(w-z) • A) := by
    apply hK.eventually_forall_of_forall_eventually
    intro w hw
    have hu : IsUnit (1 + (w-z) • resolvent hp ψ z) :=
      (mem_resolventSet_iff_isUnit_transition hp ψ z w hzψ).mp (hKs hw)
    exact (hc.continuousAt (x := (resolvent hp ψ z, w))).eventually
      (Units.isOpen.mem_nhds hu)
  filter_upwards [ht.eventually he] with k hk w hw
  exact (mem_resolventSet_iff_isUnit_transition hp (φ k) z w (hzφ k)).mpr (hk w hw)

/-- Bounded coefficient limits give locally uniform norm-resolvent limits
without any supplied reference parameter or smallness hypothesis. -/
theorem tendstoLocallyUniformlyOn_resolvent_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → PairSpace p) (ψ : PairSpace p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n))) :
    TendstoLocallyUniformlyOn (fun k z => resolvent hp (φ k) z) (resolvent hp ψ) l
      (resolventSet hp ψ) := by
  obtain ⟨H, hH, h⟩ := exists_height_resolvent_tendsto_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂
  have hz := h ((H : ℂ)*I) (by simp [abs_of_pos hH])
  exact tendstoLocallyUniformlyOn_resolvent_of_reference hp φ ψ ((H : ℂ)*I) hz.2.1 hz.1 hz.2.2

/-- The limit's compact resolvent subsets eventually remain spectral-free
under bounded coefficientwise perturbations. -/
theorem eventually_compact_subset_resolventSet_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → PairSpace p) (ψ : PairSpace p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n)))
    (K : Set ℂ) (hK : IsCompact K) (hKs : K ⊆ resolventSet hp ψ) :
    ∀ᶠ k in l, K ⊆ resolventSet hp (φ k) := by
  obtain ⟨H, hH, h⟩ := exists_height_resolvent_tendsto_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂
  have hz := h ((H : ℂ)*I) (by simp [abs_of_pos hH])
  exact eventually_compact_subset_resolventSet_of_reference hp φ ψ ((H : ℂ)*I)
    hz.2.1 hz.1 hz.2.2 K hK hKs

/-- Circle contour operators converge in operator norm under bounded
coefficientwise convergence whenever the limit circle is spectral-free. -/
theorem tendsto_resolventCircleIntegral_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → PairSpace p) (ψ : PairSpace p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp ψ) :
    Tendsto (fun k => resolventCircleIntegral hp (φ k) c r) l
      (𝓝 (resolventCircleIntegral hp ψ c r)) := by
  have hloc := tendstoLocallyUniformlyOn_resolvent_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂
  have hunif := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere c r)).mp
    (hloc.mono hc)
  have hev := eventually_compact_subset_resolventSet_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂
    (sphere c r) (isCompact_sphere c r) hc
  have hcont : ∀ᶠ k in l, ContinuousOn (resolvent hp (φ k)) (sphere c r) :=
    hev.mono fun k hk => (analyticOnNhd_resolvent hp (φ k)).continuousOn.mono hk
  exact (hunif.tendsto_circleIntegral_of_continuousOn hr hcont).const_smul (2*Real.pi*I : ℂ)⁻¹

end NLS.ZakharovShabat
