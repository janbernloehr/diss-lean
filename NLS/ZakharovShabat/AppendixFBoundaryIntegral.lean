import NLS.ZakharovShabat.SourceLemmaF2

/-! # Boundary integrals in the proof of F.2

The actual polygonal integral is the difference of endpoint averages.
Consequently changing the boundary point adds the full path integral,
and the same source neighborhood gives analyticity at both endpoints.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- The actual finite path integral equals the difference of the two literal endpoint averages. -/
theorem polygonalIntegral_eq_endpointAverage_sub (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (μ ν : ℂ)
    (hμ : μ ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    polygonalIntegral (sourceAbelianDifferential hp hp1 ψ)
        (sourceCanonicalRootDomain hp hp1 ψ) μ ν =
      sourceAbelianEndpointAverage hp hp1 n ν ψ-sourceAbelianEndpointAverage hp hp1 n μ ψ := by
  obtain ⟨E⟩ := C.charts ψ hψ
  rw [C.endpointAverage_eq ψ hψ n ν hν,C.endpointAverage_eq ψ hψ n μ hμ]
  exact polygonalIntegral_eq_sub (sourceAbelianDifferential hp hp1 ψ)
    (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ))
    (sourceCanonicalRootDomain hp hp1 ψ) (C.discs.isOpen_rootDomain ψ hψ)
    (C.discs.isConnected_rootDomain ψ hψ).isPreconnected
    (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ).continuousOn
    (fun z hz => sourceFullAbelianPrimitive_hasDerivAt E n z hz) μ ν hμ hν

/-- Changing the evaluation point retains the full common-path coefficient. -/
theorem endpointAverage_eq_add_polygonalIntegral (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (μ ν : ℂ)
    (hμ : μ ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAbelianEndpointAverage hp hp1 n ν ψ =
      sourceAbelianEndpointAverage hp hp1 n μ ψ +
        polygonalIntegral (sourceAbelianDifferential hp hp1 ψ)
          (sourceCanonicalRootDomain hp hp1 ψ) μ ν := by
  rw [C.polygonalIntegral_eq_endpointAverage_sub ψ hψ n μ ν hμ hν]
  ring

/-- One source ball works for all pairs of boundary points and every signed index. -/
theorem boundaryPolygonalIntegral_analytic (n : ℤ) (μ ν : ℂ)
    (hμ : μ ∈ sphere (C.discs.center n) (C.discs.outer n))
    (hν : ν ∈ sphere (C.discs.center n) (C.discs.outer n)) :
    AnalyticOnNhd ℂ (fun ψ => polygonalIntegral (sourceAbelianDifferential hp hp1 ψ)
      (sourceCanonicalRootDomain hp hp1 ψ) μ ν)
      (ball C.discs.source.val C.discs.sourceRadius) := by
  intro ψ hψ
  apply ((C.sourceLemmaF2 n ν hν ψ hψ).sub (C.sourceLemmaF2 n μ hμ ψ hψ)).congr
  filter_upwards [isOpen_ball.mem_nhds hψ] with χ hχ
  exact (C.polygonalIntegral_eq_endpointAverage_sub χ hχ n μ ν
    (C.circle_root n χ hχ μ hμ) (C.circle_root n χ hχ ν hν)).symm

/-- Any pointwise choice of a spectral endpoint gives the same analytic boundary integral. -/
theorem selectedEndpointIntegral_analytic (n : ℤ) (a : CoeffPair p → ℂ) (ν : ℂ)
    (ha : ∀ ψ ∈ ball C.discs.source.val C.discs.sourceRadius,
      a ψ ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hν : ν ∈ sphere (C.discs.center n) (C.discs.outer n)) :
    AnalyticOnNhd ℂ (fun ψ => sourceAbelianEndpointIntegral hp hp1 ψ (a ψ) ν)
      (ball C.discs.source.val C.discs.sourceRadius) := by
  intro ψ hψ
  apply (C.sourceLemmaF2 n ν hν ψ hψ).congr
  filter_upwards [isOpen_ball.mem_nhds hψ] with χ hχ
  rw [C.endpointIntegral_eq χ hχ n (a χ) ν (ha χ hχ) (C.circle_root n χ hχ ν hν),
    C.endpointAverage_eq χ hχ n ν (C.circle_root n χ hχ ν hν)]

/-- The literal four-path decomposition has coefficient two before the endpoint average. -/
theorem endpointAverage_fourPath_split (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (a b μ₁ μ₂ ν : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hb : b ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hμ₁ : μ₁ ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hμ₂ : μ₂ ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    2*sourceAbelianEndpointAverage hp hp1 n ν ψ =
      sourceAbelianEndpointIntegral hp hp1 ψ a μ₁ +
        polygonalIntegral (sourceAbelianDifferential hp hp1 ψ)
          (sourceCanonicalRootDomain hp hp1 ψ) μ₁ ν +
      sourceAbelianEndpointIntegral hp hp1 ψ b μ₂ +
        polygonalIntegral (sourceAbelianDifferential hp hp1 ψ)
          (sourceCanonicalRootDomain hp hp1 ψ) μ₂ ν := by
  rw [C.polygonalIntegral_eq_endpointAverage_sub ψ hψ n μ₁ ν hμ₁ hν,
    C.polygonalIntegral_eq_endpointAverage_sub ψ hψ n μ₂ ν hμ₂ hν,
    C.endpointIntegral_eq ψ hψ n a μ₁ ha hμ₁,
    C.endpointIntegral_eq ψ hψ n b μ₂ hb hμ₂,
    C.endpointAverage_eq ψ hψ n μ₁ hμ₁,C.endpointAverage_eq ψ hψ n μ₂ hμ₂]
  ring

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
