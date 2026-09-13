import NLS.ZakharovShabat.ParityContourReduction
import NLS.FunctionalAnalysis.FiniteSpectralDeterminant

/-!
# Analytic determinants on parity contour ranges

The intrinsic parity determinant agrees with its local expression on a fixed
finite-dimensional range. Analyticity is on the actual subspace of even-supported
potentials; the original unbounded operator is retained through its domain lift.
-/

noncomputable section
open Complex Metric Topology Filter
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The intrinsic determinant of the original contour restriction in one parity. -/
def parityContourDeterminant (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (R : ℝ) (r : ℤ) (z : ℂ) : ℂ :=
  ((reducedParityContourOperator hp φ φ c R r).toLinearMap-z • 1).det

/-- Local projection transport conjugates the parity reductions. -/
theorem reducedParityContourOperator_conjugate (hp : p ≠ ⊤) (φ ψ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (hψ : ψ ∈ pairParitySubspace 0)
    (c : ℂ) (R : ℝ) (r : ℤ) (hR : 0 ≤ R)
    (hcφ : sphere c R ⊆ resolventSet hp φ) (hcψ : sphere c R ⊆ resolventSet hp ψ)
    (hu : IsUnit (ProjectionTransport.transport (parityContourProjection hp φ c R r)
      (parityContourProjection hp ψ c R r))) :
    let e := ProjectionTransport.rangeEquivalence _ _
      (parityContourProjection_idempotent hp φ hφ c R r hR hcφ)
      (parityContourProjection_idempotent hp ψ hψ c R r hR hcψ) hu
    e.toLinearEquiv.conjAlgEquiv ℂ (reducedParityContourOperator hp φ ψ c R r).toLinearMap =
      (reducedParityContourOperator hp ψ ψ c R r).toLinearMap := by
  intro e
  have he (x : (parityContourProjection hp φ c R r).range) :
      (e x : PairSpace p) = ProjectionTransport.transport (parityContourProjection hp φ c R r)
        (parityContourProjection hp ψ c R r) x := ProjectionTransport.rangeEquivalence_apply _ _ _ _ hu x
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (e (reducedParityContourOperator hp φ ψ c R r (e.symm x)) : PairSpace p) = _
  rw [he, transport_reducedParityContourOperator hp φ ψ hφ hψ c R r hR hcφ hcψ hu,
    ← he, e.apply_symm_apply]
  exact (reducedParityContourOperator_self_apply hp ψ hψ c R r hR hcψ x).symm

/-- The parity determinant has the same normalization on every admissible local reference range. -/
theorem parityContourDeterminant_eq_reduced (hp : p ≠ ⊤) (φ ψ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (hψ : ψ ∈ pairParitySubspace 0)
    (c : ℂ) (R : ℝ) (r : ℤ) (hR : 0 ≤ R)
    (hcφ : sphere c R ⊆ resolventSet hp φ) (hcψ : sphere c R ⊆ resolventSet hp ψ)
    (hu : IsUnit (ProjectionTransport.transport (parityContourProjection hp φ c R r)
      (parityContourProjection hp ψ c R r))) (z : ℂ) :
    parityContourDeterminant hp ψ c R r z =
      ((reducedParityContourOperator hp φ ψ c R r).toLinearMap-z • 1).det := by
  let e := ProjectionTransport.rangeEquivalence _ _
    (parityContourProjection_idempotent hp φ hφ c R r hR hcφ)
    (parityContourProjection_idempotent hp ψ hψ c R r hR hcψ) hu
  have he := reducedParityContourOperator_conjugate hp φ ψ hφ hψ c R r hR hcφ hcψ hu
  change e.toLinearEquiv.conjAlgEquiv ℂ (reducedParityContourOperator hp φ ψ c R r).toLinearMap = _ at he
  unfold parityContourDeterminant
  rw [← he]
  exact FiniteSpectralDeterminant.shifted_det_conj e.toLinearEquiv _ z

/-- The intrinsic determinant is jointly analytic in the parameter and the even-supported potential. -/
theorem analyticAt_parityContourDeterminant (hp : p ≠ ⊤) (φ : pairParitySubspace (p := p) 0)
    (c : ℂ) (R : ℝ) (r : ℤ) (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ) (z : ℂ) :
    AnalyticAt ℂ (fun t : ℂ × pairParitySubspace (p := p) 0 =>
      parityContourDeterminant hp t.2 c R r t.1) (z,φ) := by
  let := finiteDimensional_range_parityContourProjection hp φ φ.property c R r hR hc
  have hid := parityContourProjection_idempotent hp φ φ.property c R r hR hc
  have hu : IsUnit (ProjectionTransport.transport (parityContourProjection hp φ c R r)
      (parityContourProjection hp φ c R r)) := by
    rw [ProjectionTransport.transport_self _ hid]
    exact isUnit_one
  have hsub : AnalyticAt ℂ (fun t : ℂ × pairParitySubspace (p := p) 0 => (t.2 : PairSpace p)) (z,φ) :=
    ((pairParitySubspace (p := p) 0).subtypeL.analyticAt φ).comp (analyticAt_snd (p := (z,φ)))
  have ha := FiniteSpectralDeterminant.analyticAt_shifted_det
    ((analyticAt_reducedParityContourOperator hp φ φ c R r hR hc hu).comp
      (f := fun t : ℂ × pairParitySubspace (p := p) 0 => (t.2 : PairSpace p)) hsub)
    (analyticAt_fst (p := (z,φ)))
  have hnear := ProjectionTransport.eventually_isUnit_transport
    (analyticAt_parityContourProjection hp φ c R r hR hc) hid
  have hcircle : ∀ᶠ ψ in 𝓝 (φ : PairSpace p), sphere c R ⊆ resolventSet hp ψ :=
    (isOpen_resolventCircleDomain hp c R).mem_nhds hc
  apply ha.congr
  filter_upwards [hsub.continuousAt.tendsto (hcircle.and hnear)] with t ht
  exact (parityContourDeterminant_eq_reduced hp φ t.2 φ.property t.2.property c R r hR hc ht.1 ht.2 t.1).symm

end NLS.ZakharovShabat
