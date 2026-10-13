import NLS.ZakharovShabat.SourceAuxiliaryContourDomains

/-!
# Ranks of actual auxiliary contour restrictions

Range equivalences identify the original restricted integrals with the
ordinary boundary projections at the phase-transformed potential. Their ranks
therefore count full original auxiliary Jordan multiplicities.
-/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The auxiliary condition is the ordinary condition after the inverse phase. -/
theorem auxiliarySpace_eq_comap_phase (b : BoundaryCondition) :
    auxiliarySpace (p := p) b = (b.space).comap
      (auxiliaryPhase (Coeff p)).symm.toContinuousLinearEquiv.toLinearMap := by
  ext a
  exact mem_auxiliarySpace b a

/-- Exact rank comparison for the actual original circle restriction. -/
theorem finrank_range_sourceAuxiliaryCircleProjection (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) :
    Module.finrank ℂ (sourceAuxiliaryCircleProjection b hp φ c r).range =
      Module.finrank ℂ (b.contourProjection hp (auxiliaryPotential (CoeffPair.toMax p φ)) c r).range := by
  have hc' : Metric.sphere c r ⊆ ZakharovShabat.resolventSet hp (CoeffPair.toMax p φ) := by
    rwa [sourceResolventSet_eq] at hc
  have ht : Metric.sphere c r ⊆ ZakharovShabat.resolventSet hp (auxiliaryPotential (CoeffPair.toMax p φ)) :=
    fun z hz => (mem_resolventSet_auxiliaryPotential_iff hp _ z).mp (hc' hz)
  change Module.finrank ℂ (sourceAuxiliaryCompression b (sourceResolventCircleIntegral hp φ c r)).range = _
  rw [(sourceAuxiliaryCompressionRangeEquiv b _
    (sourceAuxiliaryProjection_commute_circleIntegral b hp φ hφ c r hr hc)
    (sourceResolventCircleIntegral_idempotent hp φ c r hr hc)).toLinearEquiv.finrank_eq,
    sourceResolventCircleIntegral_eq_conj hp φ c r hr hc]
  erw [(ConjugatedRanges.rangeInfEquiv (CoeffPair.toMax p)
    (resolventCircleIntegral hp (CoeffPair.toMax p φ) c r) (b.auxiliarySpace)).finrank_eq]
  rw [resolventCircleIntegral_auxiliaryPhase_conj hp _ c r hr hc', auxiliarySpace_eq_comap_phase]
  erw [(ConjugatedRanges.rangeInfEquiv (auxiliaryPhase (Coeff p)).symm.toContinuousLinearEquiv
    (resolventCircleIntegral hp (auxiliaryPotential (CoeffPair.toMax p φ)) c r) b.space).finrank_eq]
  erw [b.range_contourProjection hp _ ((auxiliaryPotential_mem_dirichlet_iff _).mpr hφ) c r hr ht]
  rfl

/-- Exact rank comparison for the actual original central rectangle restriction. -/
theorem finrank_range_sourceAuxiliaryCentralProjection (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    Module.finrank ℂ (sourceAuxiliaryCentralProjection b hp φ N).range =
      Module.finrank ℂ (b.centralProjection hp (auxiliaryPotential (CoeffPair.toMax p φ)) N).range := by
  have hc' : centralRectangleBoundary N ⊆ ZakharovShabat.resolventSet hp (CoeffPair.toMax p φ) := by
    rwa [sourceResolventSet_eq] at hc
  have ht : centralRectangleBoundary N ⊆ ZakharovShabat.resolventSet hp (auxiliaryPotential (CoeffPair.toMax p φ)) :=
    fun z hz => (mem_resolventSet_auxiliaryPotential_iff hp _ z).mp (hc' hz)
  change Module.finrank ℂ (sourceAuxiliaryCompression b (sourceCentralRectangleIntegral hp φ N)).range = _
  rw [(sourceAuxiliaryCompressionRangeEquiv b _
    (sourceAuxiliaryProjection_commute_centralIntegral b hp φ hφ N hc)
    (sourceCentralRectangleIntegral_idempotent hp φ N hc)).toLinearEquiv.finrank_eq,
    sourceCentralRectangleIntegral_eq_conj hp φ N hc]
  erw [(ConjugatedRanges.rangeInfEquiv (CoeffPair.toMax p)
    (centralRectangleIntegral hp (CoeffPair.toMax p φ) N) b.auxiliarySpace).finrank_eq]
  change Module.finrank ℂ ↥((resolventRectangleIntegral hp (CoeffPair.toMax p φ)
    (centralLowerCorner N) (centralUpperCorner N)).range ⊓ b.auxiliarySpace) = _
  rw [resolventRectangleIntegral_auxiliaryPhase_conj hp _ _ _ (by rwa [centralCorner_boundary]),
    auxiliarySpace_eq_comap_phase]
  erw [(ConjugatedRanges.rangeInfEquiv (auxiliaryPhase (Coeff p)).symm.toContinuousLinearEquiv
    (resolventRectangleIntegral hp (auxiliaryPotential (CoeffPair.toMax p φ))
      (centralLowerCorner N) (centralUpperCorner N)) b.space).finrank_eq]
  change Module.finrank ℂ ↥((centralRectangleIntegral hp (auxiliaryPotential (CoeffPair.toMax p φ)) N).range ⊓ b.space) = _
  erw [centralRectangleIntegral_eq_centralSpectralProjection hp _ N ht,
    b.range_centralProjection hp _ ((auxiliaryPotential_mem_dirichlet_iff _).mpr hφ) N]
  rfl

/-- The actual circle rank is the sum of original full-chain multiplicities. -/
theorem sourceAuxiliaryCircleProjection_rank_eq_sum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) :
    Module.finrank ℂ (sourceAuxiliaryCircleProjection b hp φ c r).range =
      ∑ z ∈ sourceAuxiliaryEnclosedSpectrum b hp φ hφ c r,
        sourceAuxiliaryAlgebraicMultiplicity b hp φ hφ z := by
  rw [finrank_range_sourceAuxiliaryCircleProjection b hp φ hφ c r hr hc]
  simp only [sourceAuxiliaryEnclosedSpectrum_eq, sourceAuxiliaryAlgebraicMultiplicity_eq,
    auxiliaryEnclosedSpectrum_eq, auxiliaryAlgebraicMultiplicity_eq]
  exact b.finrank_contour_eq_sum_enclosed hp _ _ c r hr
    (fun z hz => (mem_resolventSet_auxiliaryPotential_iff hp _ z).mp
      (by have h := hc hz; rwa [sourceResolventSet_eq] at h))

/-- The actual central rank counts original full Jordan multiplicities. -/
theorem sourceAuxiliaryCentralProjection_rank_eq_sum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    Module.finrank ℂ (sourceAuxiliaryCentralProjection b hp φ N).range =
      ∑ z ∈ sourceAuxiliaryCentralSpectrum b hp φ hφ N,
        sourceAuxiliaryAlgebraicMultiplicity b hp φ hφ z := by
  rw [finrank_range_sourceAuxiliaryCentralProjection b hp φ hφ N hc]
  simp only [sourceAuxiliaryCentralSpectrum_eq, sourceAuxiliaryAlgebraicMultiplicity_eq,
    auxiliaryCentralSpectrum_eq, auxiliaryAlgebraicMultiplicity_eq]
  exact b.finrank_range_centralProjection hp _ _ N

end NLS.ZakharovShabat
