import NLS.ComplexAnalysis.SingularEndpointPrimitiveDetour
import NLS.ZakharovShabat.SourceCriticalRootRatioPrimitiveBoundary
import NLS.ZakharovShabat.SourceCriticalRootRatioCurvedEndpointDetour

/-!
# Exact zero for arbitrary integrable half-plane detours

Full boundary limits remove the small-neighborhood and linear-
departure conditions from the endpoint comparison. Every `C¹`
connector inside one half-plane qualifies whenever its quotient
one-form is curve-integrable. The regular crossing is automatically
integrable.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A complete upper-half-plane detour between the endpoints of an
open real-type gap has zero integral for any smooth, curve-integrable
singular connectors, without a size or departure-rate condition. -/
theorem sourceCriticalRootRatio_upperIntegrableDetour_integral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let f : ℂ → ℂ := fun z =>
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z
    ∀ {a b : ℂ}
      (left : Path l a) (crossing : Path a b) (right : Path r b),
        ContDiffOn ℝ 1 left.extend (Icc 0 1) →
        ContDiffOn ℝ 1 crossing.extend (Icc 0 1) →
        ContDiffOn ℝ 1 right.extend (Icc 0 1) →
        (∀ t ∈ Ioo (0:ℝ) 1, 0 < (left.extend t).im) →
        (∀ u : I, 0 < (crossing u).im) →
        (∀ t ∈ Ioo (0:ℝ) 1, 0 < (right.extend t).im) →
        CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f) left →
        CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f) right →
        CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f)
          (sourceCurvedGapDetourPath left crossing right) ∧
        (∫ᶜ z in sourceCurvedGapDetourPath left crossing right,
          NLS.ComplexAnalysis.holomorphicOneForm f z) = 0 := by
  dsimp only
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  obtain ⟨F,hF⟩ := exists_sourceCriticalRootRatio_upperHalfPlane_primitive
    hp hp1 ψ hreal
  obtain ⟨A,hboundaryL,hboundaryR⟩ :=
    sourceCriticalRootRatio_upperPrimitive_common_boundary_limit
      hp hp1 ψ hreal n hopen F hF
  intro a b left crossing right hleft hcross hright hleftU hcrossU hrightU
    hleftInt hrightInt
  let U : Set ℂ := {z | 0 < z.im}
  have hcrossDom : range crossing ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    rintro z ⟨u,rfl⟩
    exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
      (ne_of_gt (hcrossU u))
  have hcrossInt : CurveIntegrable
      (NLS.ComplexAnalysis.holomorphicOneForm f) crossing :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ
      crossing hcross hcrossDom
  have hcrossU' (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      crossing.extend t ∈ U := by
    rw [Path.extend_apply crossing ht]
    exact hcrossU ⟨t,ht⟩
  exact NLS.ComplexAnalysis.curveIntegral_singular_detour_eq_zero_of_primitive_boundary
    f F U (fun z hz => hF z hz) left crossing right
    hleft hcross hright hleftU hcrossU' hrightU
    hleftInt hcrossInt hrightInt hboundaryL hboundaryR

/-- A complete lower-half-plane detour between the endpoints of an
open real-type gap has zero integral for any smooth, curve-integrable
singular connectors, without a size or departure-rate condition. -/
theorem sourceCriticalRootRatio_lowerIntegrableDetour_integral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let f : ℂ → ℂ := fun z =>
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z
    ∀ {a b : ℂ}
      (left : Path l a) (crossing : Path a b) (right : Path r b),
        ContDiffOn ℝ 1 left.extend (Icc 0 1) →
        ContDiffOn ℝ 1 crossing.extend (Icc 0 1) →
        ContDiffOn ℝ 1 right.extend (Icc 0 1) →
        (∀ t ∈ Ioo (0:ℝ) 1, (left.extend t).im < 0) →
        (∀ u : I, (crossing u).im < 0) →
        (∀ t ∈ Ioo (0:ℝ) 1, (right.extend t).im < 0) →
        CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f) left →
        CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f) right →
        CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f)
          (sourceCurvedGapDetourPath left crossing right) ∧
        (∫ᶜ z in sourceCurvedGapDetourPath left crossing right,
          NLS.ComplexAnalysis.holomorphicOneForm f z) = 0 := by
  dsimp only
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  obtain ⟨F,hF⟩ := exists_sourceCriticalRootRatio_lowerHalfPlane_primitive
    hp hp1 ψ hreal
  obtain ⟨A,hboundaryL,hboundaryR⟩ :=
    sourceCriticalRootRatio_lowerPrimitive_common_boundary_limit
      hp hp1 ψ hreal n hopen F hF
  intro a b left crossing right hleft hcross hright hleftU hcrossU hrightU
    hleftInt hrightInt
  let U : Set ℂ := {z | z.im < 0}
  have hcrossDom : range crossing ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    rintro z ⟨u,rfl⟩
    exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
      (ne_of_lt (hcrossU u))
  have hcrossInt : CurveIntegrable
      (NLS.ComplexAnalysis.holomorphicOneForm f) crossing :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ
      crossing hcross hcrossDom
  have hcrossU' (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      crossing.extend t ∈ U := by
    rw [Path.extend_apply crossing ht]
    exact hcrossU ⟨t,ht⟩
  exact NLS.ComplexAnalysis.curveIntegral_singular_detour_eq_zero_of_primitive_boundary
    f F U (fun z hz => hF z hz) left crossing right
    hleft hcross hright hleftU hcrossU' hrightU
    hleftInt hcrossInt hrightInt hboundaryL hboundaryR

end NLS.ZakharovShabat
