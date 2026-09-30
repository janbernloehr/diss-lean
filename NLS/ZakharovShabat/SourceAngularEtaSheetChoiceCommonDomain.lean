import NLS.ZakharovShabat.SourceAngularEtaSheetChoicePathPeriod

/-!
# Actual Dirichlet eta values across normalized root charts

At each complex source the original normalized psi family supplies a
common family of isolating discs. On every open gap, two integrable
endpoint paths computed in regular charts matching the actual Dirichlet
anti-discriminant give eta values differing by an integer multiple of
`2π`. No spectral primitive is an input, and terminals on the cut
interior are included.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual Dirichlet eta value is independent modulo `2π` of
the path and regular chart normalized by its anti-discriminant. The
original psi normalization constructs all remainder data on one common
family of discs, for every open gap at the given complex source. -/
theorem exists_eta_dirichlet_sheet_choice_path_periods
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hdata : ∀ n, SourceAngularEndpointSpectralData hp hp1 ψ n) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ n, 0 < r n ∧ r n < R n ∧
        sourcePeriodicSegment hp hp1 ψ n ⊆ ball (c n) (r n) ∧
        closedBall (c n) (R n) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
      ∀ n, canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n →
        ∀ w v : ℂ, w ≠ 0 → v ≠ 0 →
        let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
        μ ∈ sourceAngularRegularSheetDisc hp ψ (c n) (R n) w →
        μ ∈ sourceAngularRegularSheetDisc hp ψ (c n) (R n) v →
        sourceAngularRootSheet hp w (μ,ψ) = sourceAntiDiscriminantCandidate hp hp1 ψ μ →
        sourceAngularRootSheet hp v (μ,ψ) = sourceAntiDiscriminantCandidate hp hp1 ψ μ →
        ∀ (γ κ : Path
          (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) μ),
          ContDiffOn ℝ 1 γ.extend (Icc 0 1) → ContDiffOn ℝ 1 κ.extend (Icc 0 1) →
          (∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceAngularRegularSheetDisc hp ψ (c n) (R n) w) →
          (∀ t ∈ Ioo (0:ℝ) 1, κ.extend t ∈ sourceAngularRegularSheetDisc hp ψ (c n) (R n) v) →
          CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
            (sourceAngularRootSheet hp w) (z,ψ))) γ →
          CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
            (sourceAngularRootSheet hp v) (z,ψ))) κ →
          CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w)) γ →
          CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ v)) κ →
          ∃ k : ℤ, sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ-
            sourceAngularPathIntegral n s (sourceAngularRootSheet hp v) ψ κ = k*(2*Real.pi) := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_eta_remainder_sheet_primitive_data ψ hψ hdata
  refine ⟨c,r,R,hgeom,?_⟩
  intro n hgap w v hw hv μ hb hb' heq heq' γ κ hγ hκ hγD hκD hIntγ hIntκ hmodelγ hmodelκ
  obtain ⟨F,hF⟩ := hprim n hgap
  obtain ⟨E,hE⟩ := hF w hw
  obtain ⟨J,hJ⟩ := hF v hv
  have hseg := (hgeom n).2.2.1.trans (ball_subset_ball (hgeom n).2.1.le)
  have hgap' : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hgap)
  exact hE.endpoint_pathIntegral_sub_eq_int_two_pi_of_sheet_eq hJ hseg hseg
    (hgeom n).2.2.2 (hgeom n).2.2.2 (hdata n) hgap' hw hv hb hb' (heq.trans heq'.symm)
    γ κ hγ hκ hγD hκD hIntγ hIntκ hmodelγ hmodelκ

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
