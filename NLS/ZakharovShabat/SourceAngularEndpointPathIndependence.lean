import NLS.ComplexAnalysis.PrimitiveBoundaryPathIntegral
import NLS.ZakharovShabat.SourceAngularPrimitiveBoundary

/-!
# Actual angular path independence with singular endpoints

Common relative primitive limits make angular integrals independent
of every integrable C¹ connector in the entire isolating cut
complement. Either end may be a periodic endpoint or a regular point.
The primitive and its boundary limits are derived from the actual
off-diagonal psi normalization and spectral endpoint data.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAngular_pathIntegral_eq_of_endpoint_primitive
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
    {a b : ℂ}
    (ha : a ∈ (ball c R \ sourcePeriodicSegment hp hp1 ψ m) ∪
      {canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m})
    (hb : b ∈ (ball c R \ sourcePeriodicSegment hp hp1 ψ m) ∪
      {canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m})
    (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁D : ∀ t ∈ Ioo (0:ℝ) 1, γ₁.extend t ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m)
    (hγ₂D : ∀ t ∈ Ioo (0:ℝ) 1, γ₂.extend t ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m)
    (hint₁ : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ₁)
    (hint₂ : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ₂) :
    sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₁ =
      sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₂ := by
  let D := ball c R \ sourcePeriodicSegment hp hp1 ψ m
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  obtain ⟨A,B,hA,hB⟩ := exists_sourceAngular_primitive_endpoint_limits
    hp hp1 n m s ψ c R hseg hother hdata hgap F hF
  have hboundary (z : ℂ) (hz : z ∈ D ∪ ({l,r} : Set ℂ)) :
      ∃ C : ℂ, Tendsto F (𝓝[D] z) (𝓝 C) := by
    rcases hz with hz | hz
    · exact ⟨F z,(hF z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩
    · simp only [mem_insert_iff,mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨A,hA⟩
      · exact ⟨B,hB⟩
  obtain ⟨C,hC⟩ := hboundary a ha
  obtain ⟨E,hE⟩ := hboundary b hb
  exact curveIntegral_eq_of_primitive_boundary_ends _ F D hF γ₁ γ₂
    hγ₁ hγ₂ hγ₁D hγ₂D hint₁ hint₂ hC hE

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- At each complex source with the actual endpoint data, one family
of discs gives path independence for every off-diagonal integral on
every noncollapsed gap, including singular starting and terminal
endpoints. Integrability is already proved for the controlled endpoint
connectors and remains explicit for arbitrary C¹ paths. -/
theorem exists_angular_endpoint_pathIndependence
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
        ∀ {a b : ℂ},
          a ∈ (ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m) ∪
            {canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
              canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} →
          b ∈ (ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m) ∪
            {canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
              canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} →
          ∀ (γ₁ γ₂ : Path a b),
            ContDiffOn ℝ 1 γ₁.extend (Icc 0 1) → ContDiffOn ℝ 1 γ₂.extend (Icc 0 1) →
            (∀ t ∈ Ioo (0:ℝ) 1, γ₁.extend t ∈ ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m) →
            (∀ t ∈ Ioo (0:ℝ) 1, γ₂.extend t ∈ ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m) →
            CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
              (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ₁ →
            CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
              (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ₂ →
            sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₁ =
              sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₂ := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_angular_discComplement_primitives ψ hψ
  refine ⟨c,r,R,hgeom,?_⟩
  intro n m hmn hgap a b ha hb γ₁ γ₂ hγ₁ hγ₂ hγ₁D hγ₂D hint₁ hint₂
  obtain ⟨F,hF⟩ := hprim n m hmn
  exact sourceAngular_pathIntegral_eq_of_endpoint_primitive hp hp1 n m s ψ (c m) (R m)
    ((hgeom m).2.2.1.trans (ball_subset_ball (hgeom m).2.1.le)) (hgeom m).2.2.2
    (hdata m) hgap F hF ha hb γ₁ γ₂ hγ₁ hγ₂ hγ₁D hγ₂D hint₁ hint₂

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
