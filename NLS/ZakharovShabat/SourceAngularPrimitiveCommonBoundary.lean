import NLS.ComplexAnalysis.CosinePrimitiveEndpointAgreement
import NLS.ZakharovShabat.SourceAngularPrimitiveBoundary
import NLS.ZakharovShabat.SourceAngularCollapsedPathIntegral

/-!
# Equal periodic endpoint values of actual angular primitives

The selected-root decomposition has an analytic numerator across the
whole complex gap. The cosine comparison therefore makes the two
relative endpoint values of a full cut-complement primitive equal.
Consequently every integrable C¹ path between the periodic endpoints
has zero off-diagonal angular integral on both canonical sheet signs.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual endpoint values of a single-valued angular primitive
coincide also at complex sources. No additional side-integral or
endpoint-equality assumption is supplied. -/
theorem exists_sourceAngular_primitive_common_endpoint_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (F : ℂ → ℂ)
    (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m,
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z) :
    ∃ A : ℂ,
      Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ m]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A) ∧
      Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ m]
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let τ := (l+r)/2
  let δ := (r-l)/2
  have hl : τ-δ = l := by dsimp [τ,δ]; ring
  have hr : τ+δ = r := by dsimp [τ,δ]; ring
  have hδ : δ ≠ 0 := div_ne_zero (sub_ne_zero.mpr hgap.symm) (by norm_num)
  obtain ⟨A,B,hA,hB⟩ := exists_sourceAngular_primitive_endpoint_limits
    hp hp1 n m s ψ c R hseg hother hdata hgap F hF
  have hab : A = B := by
    apply primitive_cosine_gap_boundary_values_eq
      (sourceAngularGapNumerator hp hp1 n m s ψ) (sourceStandardRoot hp hp1 ψ m)
      F (ball c R) τ δ A B isOpen_ball hδ
    · rw [hl,hr]
      exact hseg
    · exact (sourceAngularGapNumerator_analyticOnNhd hp hp1 n m s ψ hdata.analytic_omitted).mono
        (fun z hz => hother (ball_subset_closedBall hz))
    · rw [hl,hr]
      intro z hz
      exact (sourceStandardRoot_analyticAt hp hp1 ψ m z hz.2).continuousAt.continuousWithinAt
    · rw [hl,hr]
      intro z hz
      exact sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ m z hz.2
    · rw [hl,hr]
      intro z hz
      rw [← sourceAngularIntegrand_eq_gapNumerator_div_standardRoot hp hp1 n m s ψ z]
      exact hF z hz
    · rw [hl,hr]
      exact hA
    · rw [hl,hr]
      exact hB
  exact ⟨A,hA,hab.symm ▸ hB⟩

/-- An integrable connector from the left periodic endpoint to either
periodic endpoint has zero actual angular integral on both sheet signs.
This includes loops based at the singular left endpoint. -/
theorem sourceAngular_periodicEndpoint_pathIntegral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (F : ℂ → ℂ)
    (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m,
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z)
    {b : ℂ}
    (hb : b ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} : Set ℂ))
    (γ : Path
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m)
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ) :
    sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ = 0 ∧
      sourceAngularPathIntegral n s (fun t => -sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ = 0 := by
  obtain ⟨A,hA,hB⟩ := exists_sourceAngular_primitive_common_endpoint_limit
    hp hp1 n m s ψ c R hseg hother hdata hgap F hF
  have hend : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ m] b) (𝓝 A) := by
    simp only [mem_insert_iff,mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact hA
    · exact hB
  have hzero : sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ = 0 :=
    curveIntegral_eq_zero_of_primitive_boundary_ends _ F _ hF γ hγ hγD hint hA hend
  exact ⟨hzero,by rw [sourceAngularPathIntegral_neg_sheet,hzero,neg_zero]⟩

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The normalized psi family gives one all-gap family of off-diagonal
primitives whose two periodic endpoint limits agree. All primitives
and the equality follow from actual normalization and spectral data. -/
theorem exists_angular_common_endpoint_primitives
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hdata : ∀ m, SourceAngularEndpointSpectralData hp hp1 ψ m) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ m, 0 < r m ∧ r m < R m ∧
        sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (r m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m) ∧
      ∀ n m, m ≠ n →
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
        ∃ F : ℂ → ℂ, ∃ A : ℂ,
          (∀ z ∈ ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m,
            HasDerivAt F (sourceAngularIntegrand n s
              (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z) ∧
          Tendsto F (𝓝[ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m]
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A) ∧
          Tendsto F (𝓝[ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m]
            (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A) := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_angular_discComplement_primitives ψ hψ
  refine ⟨c,r,R,hgeom,?_⟩
  intro n m hmn hgap
  obtain ⟨F,hF⟩ := hprim n m hmn
  obtain ⟨A,hA,hB⟩ := exists_sourceAngular_primitive_common_endpoint_limit hp hp1 n m s ψ (c m) (R m)
    ((hgeom m).2.2.1.trans (ball_subset_ball (hgeom m).2.1.le)) (hgeom m).2.2.2 (hdata m) hgap F hF
  exact ⟨F,A,hF,hA,hB⟩

/-- The actual off-diagonal normalization gives zero endpoint integrals
on either sheet, simultaneously for all indices at each complex source.
Callers supply their integrable path, not a primitive or vanishing period. -/
theorem exists_angular_periodicEndpoint_zero
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hdata : ∀ m, SourceAngularEndpointSpectralData hp hp1 ψ m) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ m, 0 < r m ∧ r m < R m ∧
        sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (r m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m) ∧
      ∀ n m, m ≠ n →
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
        ∀ {b : ℂ}, b ∈
          ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
            canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} : Set ℂ) →
          ∀ (γ : Path
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b),
            ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
            (∀ t ∈ Ioo (0:ℝ) 1,
              γ.extend t ∈ ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m) →
            CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
              (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ →
            sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ = 0 ∧
              sourceAngularPathIntegral n s (fun t => -sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ = 0 := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_angular_discComplement_primitives ψ hψ
  refine ⟨c,r,R,hgeom,?_⟩
  intro n m hmn hgap b hb γ hγ hγD hint
  obtain ⟨F,hF⟩ := hprim n m hmn
  exact sourceAngular_periodicEndpoint_pathIntegral_eq_zero hp hp1 n m s ψ (c m) (R m)
    ((hgeom m).2.2.1.trans (ball_subset_ball (hgeom m).2.1.le)) (hgeom m).2.2.2
    (hdata m) hgap F hF hb γ hγ hγD hint

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
