import NLS.ZakharovShabat.ResolventCalculus

/-! # Resolvent normalization at an arbitrary resolvent parameter

The bounded transition operator `1 + (w-z) R(z)` is invertible exactly when
`w` belongs to the resolvent set. This transports norm-resolvent convergence
from one common parameter to every parameter of the limit resolvent set.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The bounded spectral pencil normalized by an actual resolvent at `z`. -/
def resolventTransition (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ) :
    PairSpace p →L[ℂ] PairSpace p := 1 + (w-z) • resolvent hp φ z

/-- The inverse into the domain is bijective at every resolvent parameter. -/
theorem resolventToDomain_bijective (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∈ resolventSet hp φ) : Function.Bijective (resolventToDomain hp φ z) := by
  constructor
  · intro x y h
    have he := congrArg (spectralPencil hp φ z) h
    simpa only [spectralPencil_resolventToDomain hp φ z hz] using he
  · intro f
    exact ⟨spectralPencil hp φ z f, resolventToDomain_spectralPencil hp φ z hz f⟩

/-- Factorization of the pencil through an arbitrary known resolvent. -/
theorem spectralPencil_comp_resolventToDomain_eq_transition (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hz : z ∈ resolventSet hp φ) :
    (spectralPencil hp φ w).comp (resolventToDomain hp φ z) = resolventTransition hp φ z w := by
  have he (f : Domain p) : spectralPencil hp φ w f =
      spectralPencil hp φ z f + (w-z) • domainInclusion f := by
    simp only [spectralPencil_apply, sub_smul]
    abel
  apply ContinuousLinearMap.ext
  intro f
  change spectralPencil hp φ w (resolventToDomain hp φ z f) = _
  rw [he, spectralPencil_resolventToDomain hp φ z hz]
  rfl

/-- Spectral membership is equivalent to invertibility of the transition
operator at any known resolvent parameter. -/
theorem mem_resolventSet_iff_isUnit_transition (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hz : z ∈ resolventSet hp φ) :
    w ∈ resolventSet hp φ ↔ IsUnit (resolventTransition hp φ z w) := by
  rw [← spectralPencil_comp_resolventToDomain_eq_transition hp φ z w hz, ContinuousLinearMap.isUnit_iff_bijective]
  exact (Function.Bijective.of_comp_iff (spectralPencil hp φ w)
    (resolventToDomain_bijective hp φ z hz)).symm

/-- The domain-valued resolvent changes reference by a bounded inverse. -/
theorem resolventToDomain_eq_comp_inverse_transition (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hz : z ∈ resolventSet hp φ) (hw : w ∈ resolventSet hp φ) :
    resolventToDomain hp φ w = (resolventToDomain hp φ z).comp
      (Ring.inverse (resolventTransition hp φ z w)) := by
  have hT := (mem_resolventSet_iff_isUnit_transition hp φ z w hz).mp hw
  apply ContinuousLinearMap.ext
  intro f
  apply hw.injective
  rw [spectralPencil_resolventToDomain hp φ w hw]
  symm
  change ((spectralPencil hp φ w).comp (resolventToDomain hp φ z))
    (Ring.inverse (resolventTransition hp φ z w) f) = f
  rw [spectralPencil_comp_resolventToDomain_eq_transition hp φ z w hz]
  exact congrArg (fun T : PairSpace p →L[ℂ] PairSpace p => T f)
    (Ring.mul_inverse_cancel _ hT)

/-- The full resolvent is expressed using only its bounded value at the reference point. -/
theorem resolvent_eq_comp_inverse_transition (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hz : z ∈ resolventSet hp φ) (hw : w ∈ resolventSet hp φ) :
    resolvent hp φ w = (resolvent hp φ z).comp
      (Ring.inverse (resolventTransition hp φ z w)) := by
  rw [resolvent, resolventToDomain_eq_comp_inverse_transition hp φ z w hz hw]
  exact (ContinuousLinearMap.comp_assoc _ _ _).symm

/-- Reference-point convergence also permits a moving target spectral parameter. -/
theorem eventually_mem_and_tendsto_resolvent_of_reference_and_parameter
    (hp : p ≠ ⊤) {α : Type*} {l : Filter α} (φ : α → PairSpace p) (ψ : PairSpace p)
    (z : ℂ) (hzφ : ∀ k, z ∈ resolventSet hp (φ k)) (hzψ : z ∈ resolventSet hp ψ)
    (ht : Tendsto (fun k => resolvent hp (φ k) z) l (𝓝 (resolvent hp ψ z)))
    (u : α → ℂ) (w : ℂ) (hu : Tendsto u l (𝓝 w)) (hw : w ∈ resolventSet hp ψ) :
    (∀ᶠ k in l, u k ∈ resolventSet hp (φ k)) ∧
      Tendsto (fun k => resolvent hp (φ k) (u k)) l (𝓝 (resolvent hp ψ w)) := by
  have hT : Tendsto (fun k => resolventTransition hp (φ k) z (u k)) l
      (𝓝 (resolventTransition hp ψ z w)) :=
    tendsto_const_nhds.add ((hu.sub_const z).smul ht)
  have hunit := (mem_resolventSet_iff_isUnit_transition hp ψ z w hzψ).mp hw
  have hev : ∀ᶠ k in l, u k ∈ resolventSet hp (φ k) := by
    have h := hT.eventually (Units.isOpen.mem_nhds hunit)
    exact h.mono fun k hk => (mem_resolventSet_iff_isUnit_transition hp (φ k) z (u k) (hzφ k)).mpr hk
  refine ⟨hev, ?_⟩
  have hinv := (analyticOnNhd_inverse (𝕜 := ℂ) _ hunit).continuousAt.tendsto.comp hT
  have hprod := ht.mul hinv
  rw [resolvent_eq_comp_inverse_transition hp ψ z w hzψ hw]
  apply hprod.congr'
  filter_upwards [hev] with k hk
  exact (resolvent_eq_comp_inverse_transition hp (φ k) z (u k) (hzφ k) hk).symm

/-- Norm-resolvent convergence at one common parameter implies eventual
spectral membership and convergence at every parameter of the limit resolvent set. -/
theorem eventually_mem_and_tendsto_resolvent_of_reference
    (hp : p ≠ ⊤) {α : Type*} {l : Filter α} (φ : α → PairSpace p) (ψ : PairSpace p)
    (z : ℂ) (hzφ : ∀ k, z ∈ resolventSet hp (φ k)) (hzψ : z ∈ resolventSet hp ψ)
    (ht : Tendsto (fun k => resolvent hp (φ k) z) l (𝓝 (resolvent hp ψ z)))
    (w : ℂ) (hw : w ∈ resolventSet hp ψ) :
    (∀ᶠ k in l, w ∈ resolventSet hp (φ k)) ∧
      Tendsto (fun k => resolvent hp (φ k) w) l (𝓝 (resolvent hp ψ w)) :=
  eventually_mem_and_tendsto_resolvent_of_reference_and_parameter hp φ ψ z hzφ hzψ ht
    (fun _ => w) w tendsto_const_nhds hw

end NLS.ZakharovShabat
