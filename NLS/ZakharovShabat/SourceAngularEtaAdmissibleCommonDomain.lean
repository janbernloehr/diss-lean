import NLS.ZakharovShabat.SourceAngularEtaAdmissiblePathPeriod

/-!
# Actual Dirichlet eta periods along general admissible root continuations

The original normalized psi family constructs the remainder on one
all-gap family of isolating discs. At an open gap, any two integrable C1
admissible paths with continuously continued roots normalized by the
actual Dirichlet anti-discriminant give the same eta value modulo `2π`.
At a periodic terminal no root-sign normalization is needed. Intermediate
root charts are unrestricted, and no primitive is supplied as an input.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual Dirichlet eta integral is independent modulo `2π` of
admissible path and continuous root continuation. For a regular terminal
only its anti-discriminant fixes the sign; at a periodic terminal either
sign is allowed. The terminal must lie in the chosen isolating disc. -/
theorem exists_eta_dirichlet_admissible_path_periods
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hdata : ∀ n, SourceAngularEndpointSpectralData hp hp1 ψ n) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ n, 0 < r n ∧ r n < R n ∧
        sourcePeriodicSegment hp hp1 ψ n ⊆ ball (c n) (r n) ∧
        closedBall (c n) (R n) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
      ∀ n, canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n →
        let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
        let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
        μ ∈ ball (c n) (R n) →
        ∀ Q Q' : ℂ × CoeffPair p → ℂ,
        ∀ (γ κ : Path
          (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) μ),
          SourceAngularAdmissiblePathRootData hp hp1 n ψ (c n) (R n) Q γ →
          SourceAngularAdmissiblePathRootData hp hp1 n ψ (c n) (R n) Q' κ →
          (w ≠ 0 → Q (μ,ψ) = w) → (w ≠ 0 → Q' (μ,ψ) = w) →
          ContDiffOn ℝ 1 γ.extend (Icc 0 1) → ContDiffOn ℝ 1 κ.extend (Icc 0 1) →
          CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ →
          CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q' (z,ψ))) κ →
          CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q)) γ →
          CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q')) κ →
          ∃ k : ℤ, sourceAngularPathIntegral n s Q ψ γ-sourceAngularPathIntegral n s Q' ψ κ =
            k*(2*Real.pi) := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_eta_remainder_sheet_primitive_data ψ hψ hdata
  refine ⟨c,r,R,hgeom,?_⟩
  intro n hgap μ w hμ Q Q' γ κ hQ hQ' hnorm hnorm' hγ hκ hint hint' hmodel hmodel'
  obtain ⟨F,hF⟩ := hprim n hgap
  have hseg := (hgeom n).2.2.1.trans (ball_subset_ball (hgeom n).2.1.le)
  have hother := (hgeom n).2.2.2
  have hgap' : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hgap)
  by_cases hw : w ≠ 0
  · obtain ⟨E,hE⟩ := hF w hw
    have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ n hw
    exact hE.admissible_pathIntegral_sub_eq_int_two_pi hseg hother (hdata n) hgap' hw
      ⟨hμ,hbase.1⟩ Q Q' γ κ hQ hQ' ((hnorm hw).trans hbase.2.symm)
      ((hnorm' hw).trans hbase.2.symm) hγ hκ hint hint' hmodel hmodel'
  · have hzero : sourceAntiDiscriminantCandidate hp hp1 ψ μ = 0 := not_ne_iff.mp hw
    have hend := sourceDirichletRoot_mem_periodicEndpoints_of_antiDiscriminant_eq_zero hp hp1 ψ n
      (hother (ball_subset_closedBall hμ)) hzero
    obtain ⟨E,hE⟩ := hF 1 one_ne_zero
    exact hE.admissible_periodic_terminal_pathIntegral_sub_eq_int_two_pi hseg hother (hdata n) hgap'
      hμ hend Q Q' γ κ hQ hQ' hγ hκ hint hint' hmodel hmodel'

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
