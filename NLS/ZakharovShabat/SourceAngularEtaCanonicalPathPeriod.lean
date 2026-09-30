import NLS.ZakharovShabat.SourceAngularEtaModelPathPeriod
import NLS.ZakharovShabat.SourceAngularEtaRemainderBoundary

/-!
# Actual diagonal eta path periods on the canonical sheet

The single-valued remainder cancels between two paths with common
endpoints. The logarithmic model proves that the literal diagonal
angular integrals differ by `2π ℤ`. This includes arbitrary winding,
regular paths for collapsed gaps, and integrable open-gap paths with
singular endpoints and common remainder boundary values.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Arbitrary regular canonical-sheet paths with common endpoints
have diagonal angular integrals differing by a multiple of `2π`. -/
theorem sourceAngularEta_discComplement_pathIntegral_sub_eq_int_two_pi
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (F : ℂ → ℂ) (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z)
    {a b : ℂ} (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁D : ∀ t : I, γ₁ t ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n)
    (hγ₂D : ∀ t : I, γ₂ t ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n) :
    ∃ k : ℤ, sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₁ -
      sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₂ = k*(2*Real.pi) := by
  obtain ⟨_,h₁⟩ := sourceAngularEta_discComplement_pathIntegral_decomposition
    hp hp1 n s ψ c R hother F hF γ₁ hγ₁ hγ₁D
  obtain ⟨_,h₂⟩ := sourceAngularEta_discComplement_pathIntegral_decomposition
    hp hp1 n s ψ c R hother F hF γ₂ hγ₂ hγ₂D
  obtain ⟨k,hk⟩ := sourceAngularEtaModel_regular_pathIntegral_sub_eq_int_two_pi hp hp1 n ψ
    γ₁ γ₂ hγ₁ hγ₂ (fun t => (hγ₁D t).2) (fun t => (hγ₂D t).2)
  exact ⟨k,by rw [h₁,h₂]; linear_combination hk⟩

/-- Open-gap paths with common (possibly singular) endpoints have
the same actual diagonal angular value modulo `2π`. The boundary
values concern only the proved single-valued remainder. -/
theorem sourceAngularEta_openGap_pathIntegral_sub_eq_int_two_pi_of_boundary_values
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (D : Set ℂ) (hD : D ⊆ (sourcePeriodicSegment hp hp1 ψ n)ᶜ)
    (F : ℂ → ℂ) (hF : ∀ z ∈ D,
      HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z)
    {a b A B : ℂ} (ha : a ∈ sourceAngularEtaModelEndpointDomain hp hp1 n ψ)
    (hb : b ∈ sourceAngularEtaModelEndpointDomain hp hp1 n ψ)
    (hA : Tendsto F (𝓝[D] a) (𝓝 A)) (hB : Tendsto F (𝓝[D] b) (𝓝 B))
    (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁D : ∀ t ∈ Ioo (0:ℝ) 1, γ₁.extend t ∈ D)
    (hγ₂D : ∀ t ∈ Ioo (0:ℝ) 1, γ₂.extend t ∈ D)
    (hint₁ : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ₁)
    (hint₂ : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ₂)
    (hmodel₁ : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ)) γ₁)
    (hmodel₂ : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ)) γ₂) :
    ∃ k : ℤ, sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₁ -
      sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₂ = k*(2*Real.pi) := by
  have h₁ := sourceAngularEta_pathIntegral_decomposition_of_boundary_values
    hp hp1 n s ψ D F hF γ₁ hγ₁ hγ₁D hint₁ hmodel₁ hA hB
  have h₂ := sourceAngularEta_pathIntegral_decomposition_of_boundary_values
    hp hp1 n s ψ D F hF γ₂ hγ₂ hγ₂D hint₂ hmodel₂ hA hB
  obtain ⟨k,hk⟩ := sourceAngularEtaModel_openGap_pathIntegral_sub_eq_int_two_pi hp hp1 n ψ hgap
    ha hb γ₁ γ₂ hγ₁ hγ₂ (fun t ht => hD (hγ₁D t ht)) (fun t ht => hD (hγ₂D t ht)) hmodel₁ hmodel₂
  exact ⟨k,by rw [h₁,h₂]; linear_combination hk⟩

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual normalized psi extension supplies common all-gap
domains with regular diagonal path independence modulo `2π`, for
every complex source and without requiring an open gap. -/
theorem exists_eta_regular_path_periods
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ n, 0 < r n ∧ r n < R n ∧
        sourcePeriodicSegment hp hp1 ψ n ⊆ ball (c n) (r n) ∧
        closedBall (c n) (R n) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
      ∀ n, ∀ {a b : ℂ} (γ₁ γ₂ : Path a b),
        ContDiffOn ℝ 1 γ₁.extend (Icc 0 1) → ContDiffOn ℝ 1 γ₂.extend (Icc 0 1) →
        (∀ t : I, γ₁ t ∈ ball (c n) (R n) \ sourcePeriodicSegment hp hp1 ψ n) →
        (∀ t : I, γ₂ t ∈ ball (c n) (R n) \ sourcePeriodicSegment hp hp1 ψ n) →
        ∃ k : ℤ, sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₁ -
          sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₂ = k*(2*Real.pi) := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_eta_remainder_discComplement_primitives ψ hψ
  refine ⟨c,r,R,hgeom,?_⟩
  intro n a b γ₁ γ₂ hγ₁ hγ₂ hγ₁D hγ₂D
  obtain ⟨F,hF⟩ := hprim n
  exact sourceAngularEta_discComplement_pathIntegral_sub_eq_int_two_pi hp hp1 n s ψ (c n) (R n)
    (hgeom n).2.2.2 F hF γ₁ γ₂ hγ₁ hγ₂ hγ₁D hγ₂D

/-- The actual family also supplies the primitive and its boundary
values for singular-start eta paths. A terminal outside the cut or at
either periodic endpoint is allowed; integrability of both literal
differentials is retained explicitly. -/
theorem exists_eta_openGap_endpoint_path_periods
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hdata : ∀ n, SourceAngularEndpointSpectralData hp hp1 ψ n) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ n, 0 < r n ∧ r n < R n ∧
        sourcePeriodicSegment hp hp1 ψ n ⊆ ball (c n) (r n) ∧
        closedBall (c n) (R n) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
      ∀ n, canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n →
        ∀ {b : ℂ}, b ∈ ball (c n) (R n) ∩ sourceAngularEtaModelEndpointDomain hp hp1 n ψ →
        ∀ (γ₁ γ₂ : Path
          (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) b),
          ContDiffOn ℝ 1 γ₁.extend (Icc 0 1) → ContDiffOn ℝ 1 γ₂.extend (Icc 0 1) →
          (∀ t ∈ Ioo (0:ℝ) 1, γ₁.extend t ∈ ball (c n) (R n) \ sourcePeriodicSegment hp hp1 ψ n) →
          (∀ t ∈ Ioo (0:ℝ) 1, γ₂.extend t ∈ ball (c n) (R n) \ sourcePeriodicSegment hp hp1 ψ n) →
          CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
            (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ₁ →
          CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
            (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ₂ →
          CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ)) γ₁ →
          CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ)) γ₂ →
          ∃ k : ℤ, sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₁ -
            sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₂ = k*(2*Real.pi) := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_eta_remainder_normalized_endpoint_primitives ψ hψ hdata
  refine ⟨c,r,R,hgeom,?_⟩
  intro n hgap b hb γ₁ γ₂ hγ₁ hγ₂ hγ₁D hγ₂D hint₁ hint₂ hmodel₁ hmodel₂
  obtain ⟨F,hF,hleft,hright⟩ := hprim n hgap
  let D := ball (c n) (R n) \ sourcePeriodicSegment hp hp1 ψ n
  have hterminal : ∃ B : ℂ, Tendsto F (𝓝[D] b) (𝓝 B) := by
    rcases hb.2 with hout | hend
    · exact ⟨F b,(hF b ⟨hb.1,hout⟩).continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩
    · simp only [mem_insert_iff,mem_singleton_iff] at hend
      rcases hend with rfl | rfl
      · exact ⟨0,hleft⟩
      · exact ⟨0,hright⟩
  obtain ⟨B,hB⟩ := hterminal
  exact sourceAngularEta_openGap_pathIntegral_sub_eq_int_two_pi_of_boundary_values hp hp1 n s ψ hgap
    D (fun _ hz => hz.2) F hF (Or.inr (by simp)) hb.2 hleft hB
    γ₁ γ₂ hγ₁ hγ₂ hγ₁D hγ₂D hint₁ hint₂ hmodel₁ hmodel₂

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
