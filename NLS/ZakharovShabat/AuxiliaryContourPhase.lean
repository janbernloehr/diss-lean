import NLS.ZakharovShabat.SourceAuxiliaryCounting
import NLS.ZakharovShabat.SourceResolventContours

/-!
# Auxiliary phase transport of the actual resolvent and contour integrals

The exact domain-to-base pencil conjugation transports the full ambient
resolvent, including its zero extension off the resolvent set. Bounded linear
maps commute with the actual operator-norm circle and rectangle integrals.
The auxiliary complementary projections therefore commute with these integrals
for Neumann-reflected potentials.
-/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem mem_resolventSet_auxiliaryPotential_iff (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    z ∈ resolventSet hp φ ↔ z ∈ resolventSet hp (auxiliaryPotential φ) := by
  change Function.Bijective (spectralPencil hp φ z) ↔ Function.Bijective (spectralPencil hp (auxiliaryPotential φ) z)
  have he : spectralPencil hp φ z ∘ (auxiliaryPhase (ScalarDomain p)).toEquiv =
      (auxiliaryPhase (Coeff p)).toEquiv ∘ spectralPencil hp (auxiliaryPotential φ) z :=
    funext (spectralPencil_auxiliaryPhase hp φ z)
  rw [← (auxiliaryPhase (ScalarDomain p)).toEquiv.bijective_comp, he]
  exact (auxiliaryPhase (Coeff p)).toEquiv.comp_bijective _

theorem resolventToDomain_auxiliaryPhase (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (a : PairSpace p) :
    resolventToDomain hp φ z (auxiliaryPhase (Coeff p) a) =
      auxiliaryPhase (ScalarDomain p) (resolventToDomain hp (auxiliaryPotential φ) z a) := by
  by_cases hz : z ∈ resolventSet hp φ
  · have ht := (mem_resolventSet_auxiliaryPotential_iff hp φ z).mp hz
    apply hz.injective
    rw [spectralPencil_resolventToDomain hp φ z hz, spectralPencil_auxiliaryPhase,
      spectralPencil_resolventToDomain hp (auxiliaryPotential φ) z ht]
  · have ht : z ∉ resolventSet hp (auxiliaryPotential φ) :=
      fun h => hz ((mem_resolventSet_auxiliaryPotential_iff hp φ z).mpr h)
    rw [resolventToDomain_eq_zero_of_notMem hp φ z hz,
      resolventToDomain_eq_zero_of_notMem hp (auxiliaryPotential φ) z ht]
    change 0 = auxiliaryPhase (ScalarDomain p) 0
    exact (map_zero _).symm

theorem resolvent_auxiliaryPhase_conj (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    resolvent hp φ z = (auxiliaryPhase (Coeff p)).toContinuousLinearEquiv.conjContinuousAlgEquiv
      (resolvent hp (auxiliaryPotential φ) z) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨a,rfl⟩ := (auxiliaryPhase (Coeff p)).surjective x
  change domainInclusion (resolventToDomain hp φ z (auxiliaryPhase (Coeff p) a)) =
    auxiliaryPhase (Coeff p) (resolvent hp (auxiliaryPotential φ) z
      ((auxiliaryPhase (Coeff p)).symm (auxiliaryPhase (Coeff p) a)))
  rw [LinearIsometryEquiv.symm_apply_apply, resolventToDomain_auxiliaryPhase, domainInclusion_auxiliaryPhase]
  rfl

theorem resolventCircleIntegral_auxiliaryPhase_conj (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : Metric.sphere c r ⊆ resolventSet hp φ) :
    resolventCircleIntegral hp φ c r =
      (auxiliaryPhase (Coeff p)).toContinuousLinearEquiv.conjContinuousAlgEquiv
        (resolventCircleIntegral hp (auxiliaryPotential φ) c r) := by
  have hc' : Metric.sphere c r ⊆ resolventSet hp (auxiliaryPotential φ) :=
    fun z hz => (mem_resolventSet_auxiliaryPotential_iff hp φ z).mp (hc hz)
  let A := (auxiliaryPhase (Coeff p)).toContinuousLinearEquiv.conjContinuousAlgEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  change _ = A ((2*Real.pi*Complex.I : ℂ)⁻¹ • ∮ z in C(c,r), resolvent hp (auxiliaryPotential φ) z)
  rw [map_smul, NLS.CircleIntegral.map A (circleIntegrable_resolvent hp _ c r hr hc')]
  have he : resolvent hp φ = fun z => A (resolvent hp (auxiliaryPotential φ) z) :=
    funext (resolvent_auxiliaryPhase_conj hp φ)
  rw [resolventCircleIntegral, he]

theorem resolventRectangleIntegral_auxiliaryPhase_conj (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) :
    resolventRectangleIntegral hp φ z w =
      (auxiliaryPhase (Coeff p)).toContinuousLinearEquiv.conjContinuousAlgEquiv
        (resolventRectangleIntegral hp (auxiliaryPotential φ) z w) := by
  have hc' : RectangleIntegral.boundary z w ⊆ resolventSet hp (auxiliaryPotential φ) :=
    fun ζ hζ => (mem_resolventSet_auxiliaryPotential_iff hp φ ζ).mp (hc hζ)
  let A := (auxiliaryPhase (Coeff p)).toContinuousLinearEquiv.conjContinuousAlgEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  change _ = A ((2*Real.pi*Complex.I : ℂ)⁻¹ • RectangleIntegral.integral (resolvent hp (auxiliaryPotential φ)) z w)
  rw [map_smul, RectangleIntegral.map A (rectangleIntegrable_resolvent hp _ z w hc')]
  have he : resolvent hp φ = fun ζ => A (resolvent hp (auxiliaryPotential φ) ζ) :=
    funext (resolvent_auxiliaryPhase_conj hp φ)
  rw [resolventRectangleIntegral, he]

namespace BoundaryCondition

def auxiliaryProjection (b : BoundaryCondition) : PairSpace p →L[ℂ] PairSpace p :=
  (auxiliaryPhase (Coeff p)).toContinuousLinearEquiv.conjContinuousAlgEquiv (b.projection)

theorem auxiliaryProjection_mem (b : BoundaryCondition) (a : PairSpace p) :
    auxiliaryProjection b a ∈ auxiliarySpace b := by
  change auxiliaryPhase (Coeff p) (b.projection ((auxiliaryPhase (Coeff p)).symm a)) ∈ auxiliarySpace b
  exact ⟨_,b.projection_mem _,rfl⟩

theorem auxiliaryProjection_eq_self (b : BoundaryCondition) (a : PairSpace p) (ha : a ∈ auxiliarySpace b) :
    auxiliaryProjection b a = a := by
  change auxiliaryPhase (Coeff p) (b.projection ((auxiliaryPhase (Coeff p)).symm a)) = a
  rw [b.projection_eq_self ((mem_auxiliarySpace b a).mp ha), LinearIsometryEquiv.apply_symm_apply]

theorem auxiliaryProjection_commute_circleIntegral (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : PairSpace p) (hφ : φ ∈ neumannSubspace) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    Commute (auxiliaryProjection b) (resolventCircleIntegral hp φ c r) := by
  rw [resolventCircleIntegral_auxiliaryPhase_conj hp φ c r hr hc]
  exact (b.projection_commute_contour hp (auxiliaryPotential φ)
    ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) c r hr
    (fun z hz => (mem_resolventSet_auxiliaryPotential_iff hp φ z).mp (hc hz))).map
      ((auxiliaryPhase (Coeff p)).toContinuousLinearEquiv.conjContinuousAlgEquiv)

theorem auxiliaryProjection_commute_centralIntegral (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : PairSpace p) (hφ : φ ∈ neumannSubspace) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ ZakharovShabat.resolventSet hp φ) :
    Commute (auxiliaryProjection b) (centralRectangleIntegral hp φ N) := by
  have ht : centralRectangleBoundary N ⊆ ZakharovShabat.resolventSet hp (auxiliaryPotential φ) :=
    fun z hz => (mem_resolventSet_auxiliaryPotential_iff hp φ z).mp (hc hz)
  change Commute (auxiliaryProjection b) (resolventRectangleIntegral hp φ (centralLowerCorner N) (centralUpperCorner N))
  rw [resolventRectangleIntegral_auxiliaryPhase_conj hp φ _ _ (by rwa [centralCorner_boundary])]
  change Commute (auxiliaryProjection b)
    ((auxiliaryPhase (Coeff p)).toContinuousLinearEquiv.conjContinuousAlgEquiv
      (centralRectangleIntegral hp (auxiliaryPotential φ) N))
  rw [centralRectangleIntegral_eq_centralSpectralProjection hp _ N ht]
  exact (b.projection_commute_clusterProjection hp (auxiliaryPotential φ)
    ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) _).map
      ((auxiliaryPhase (Coeff p)).toContinuousLinearEquiv.conjContinuousAlgEquiv)

end BoundaryCondition

end NLS.ZakharovShabat
