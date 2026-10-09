import NLS.ComplexAnalysis.PolygonalEndpointIntegral
import NLS.ComplexAnalysis.PrimitiveBoundaryPathIntegral
import NLS.ZakharovShabat.SourceFullAbelianUniformEndpoints

/-! # The literal endpoint integrals defining the source primitive

The integrals are defined from finite sums of actual segment integrals,
then limits approaching the selected endpoint through the cut complement.
Their identification with the canonical primitive proves existence and
path independence, including at collapsed complex gaps.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The physical differential Delta'/sqrt_c(Delta^2-4). -/
def sourceAbelianDifferential (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z/sourceCanonicalRoot hp hp1 ψ z

/-- An improper integral from an endpoint, defined through actual polygonal integrals. -/
def sourceAbelianEndpointIntegral (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (a ν : ℂ) : ℂ :=
  endpointPolygonalIntegral (sourceAbelianDifferential hp hp1 ψ) (sourceCanonicalRootDomain hp hp1 ψ) a ν

/-- The literal average of the two endpoint integrals in Appendix F. -/
def sourceAbelianEndpointAverage (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ν : ℂ) (ψ : CoeffPair p) : ℂ :=
  (sourceAbelianEndpointIntegral hp hp1 ψ
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) ν+
    sourceAbelianEndpointIntegral hp hp1 ψ
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) ν)/2

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- Endpoint limits are genuine: every endpoint lies in the closure of the cut complement. -/
theorem endpoint_mem_closure_rootDomain (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ)) :
    a ∈ closure (sourceCanonicalRootDomain hp hp1 ψ) := by
  have hdense := dense_complex_segment_complement
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
  have haB := C.endpoint_mem_ball n ψ hψ a ha
  have hcl := hdense.open_subset_closure_inter isOpen_ball haB
  apply closure_mono (sourceAbelian_discComplement_subset_rootDomain hp hp1 ψ n
    (C.discs.center n) (C.discs.outer n) (C.discs.avoids_other ψ hψ n)) hcl

/-- Every truncated polygonal integral converges to the normalized primitive value. -/
theorem tendsto_endpointPolygonalIntegral (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (a ν : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    Tendsto (fun z => polygonalIntegral (sourceAbelianDifferential hp hp1 ψ)
      (sourceCanonicalRootDomain hp hp1 ψ) z ν) (𝓝[sourceCanonicalRootDomain hp hp1 ψ] a)
        (𝓝 (sourceFullAbelianPrimitive hp hp1 W n (ν,ψ))) := by
  obtain ⟨E⟩ := C.charts ψ hψ
  have hlim := (C.fullPrimitive_endpoint_limit_openGap n n ψ hψ a ha).mono_left
    (nhdsWithin_mono a (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ))
  simp only [sub_self,mul_zero] at hlim
  have h := tendsto_polygonalIntegral_endpoint (sourceAbelianDifferential hp hp1 ψ)
    (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ)) (sourceCanonicalRootDomain hp hp1 ψ)
    (C.discs.isOpen_rootDomain ψ hψ) (C.discs.isConnected_rootDomain ψ hψ).isPreconnected
    (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ).continuousOn
    (fun z hz => sourceFullAbelianPrimitive_hasDerivAt E n z hz) a ν 0 hν hlim
  simpa only [sub_zero] using h

/-- Each of the two improper endpoint integrals equals the same canonical primitive. -/
theorem endpointIntegral_eq (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (a ν : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAbelianEndpointIntegral hp hp1 ψ a ν = sourceFullAbelianPrimitive hp hp1 W n (ν,ψ) := by
  let : NeBot (𝓝[sourceCanonicalRootDomain hp hp1 ψ] a) :=
    mem_closure_iff_nhdsWithin_neBot.mp (C.endpoint_mem_closure_rootDomain ψ hψ n a ha)
  exact (C.tendsto_endpointPolygonalIntegral ψ hψ n a ν ha hν).limUnder_eq

/-- Identification of the literal two-endpoint average, with its exact factor one half. -/
theorem endpointAverage_eq (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (ν : ℂ)
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAbelianEndpointAverage hp hp1 n ν ψ = sourceFullAbelianPrimitive hp hp1 W n (ν,ψ) := by
  rw [sourceAbelianEndpointAverage,C.endpointIntegral_eq ψ hψ n _ ν (by simp) hν,
    C.endpointIntegral_eq ψ hψ n _ ν (by simp) hν]
  ring

/-- The improper definition agrees with every integrable C1 admissible endpoint path. -/
theorem endpointCurveIntegral_eq (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (a ν : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ) (γ : Path a ν)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hpath : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hint : CurveIntegrable (holomorphicOneForm (sourceAbelianDifferential hp hp1 ψ)) γ) :
    (∫ᶜ z in γ, holomorphicOneForm (sourceAbelianDifferential hp hp1 ψ) z) =
      sourceAbelianEndpointIntegral hp hp1 ψ a ν := by
  obtain ⟨E⟩ := C.charts ψ hψ
  rw [C.endpointIntegral_eq ψ hψ n a ν ha hν]
  have hlim := (C.fullPrimitive_endpoint_limit_openGap n n ψ hψ a ha).mono_left
    (nhdsWithin_mono a (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ))
  simp only [sub_self,mul_zero] at hlim
  have h := curveIntegral_eq_sub_of_primitive_boundary_ends (sourceAbelianDifferential hp hp1 ψ)
    (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ)) (sourceCanonicalRootDomain hp hp1 ψ)
    (fun z hz => sourceFullAbelianPrimitive_hasDerivAt E n z hz) γ hγ hpath hint hlim
    (sourceFullAbelianPrimitive_hasDerivAt E n ν hν).continuousAt.continuousWithinAt.tendsto
  simpa only [sub_zero] using h

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
