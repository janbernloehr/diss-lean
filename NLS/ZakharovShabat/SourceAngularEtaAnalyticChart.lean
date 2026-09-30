import NLS.ZakharovShabat.SourceAngularEtaAnalyticRepresentative

/-! # Constructing full analytic eta charts at every complex open gap

An actual joint annulus chart and the proved source analyticity of the
spectral coordinates construct the terminal angle, full eta representative,
and endpoint integration data. The terminal angle is unrestricted: no
convex angle chart needs to contain it.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- The actual annulus and analytic coordinates supply every field of
a full local eta chart at any complex open-gap source. -/
theorem exists_local_analytic_eta_chart
    (C : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (φ : CoeffPair p) (hφ : φ ∈ V)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0)
    (hτ : AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m) φ)
    (hγsq : AnalyticAt ℂ (fun ψ : CoeffPair p => (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m)^2) φ)
    (hμ : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) V)
    (hD : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 V m))
    (hP : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 m)
      (sourceStandardRootOmittedJointDomain hp hp1 V m)) :
    ∃ U : Set (CoeffPair p), ∃ δ ε : CoeffPair p → ℂ, φ ∈ U ∧
      δ φ = canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m/2 ∧
      SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε := by
  have hμD : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m ∈
      sourceStandardRootOmittedDomain hp hp1 φ m :=
    ((C.disc_family φ hφ).contour_family.2 m).2.2.1
      (ball_subset_closedBall ((C.disc_family φ hφ).dirichlet_mem_ball m))
  obtain ⟨U,hU,hφU,hUV,δ,ε,hδ,hε,hbase,hcoords⟩ :=
    exists_local_analytic_complex_dirichlet_angle hp hp1 V C.source_open φ hφ m hgap
      hτ hγsq (hμ φ hφ) hμD hD hP
  have hdata (ψ : CoeffPair p) (hψ : ψ ∈ U) : SourceAngularEndpointSpectralData hp hp1 ψ m := by
    have hψV := hUV hψ
    have hO : IsOpen (sourceStandardRootOmittedDomain hp hp1 ψ m) := by
      have heq : sourceStandardRootOmittedDomain hp hp1 ψ m =
          (fun z : ℂ => (z,ψ)) ⁻¹' sourceStandardRootOmittedJointDomain hp hp1 V m := by
        ext z
        exact ⟨fun hz => ⟨hψV,hz⟩,And.right⟩
      rw [heq]
      exact hD.preimage (continuous_id.prodMk continuous_const)
    have havoid : sourcePeriodicSegment hp hp1 ψ m ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m :=
      (C.gap_enclosed ψ hψV).trans ((ball_subset_ball
        (C.inner_lt_outer.trans C.outer_lt_assigned).le).trans
          (ball_subset_closedBall.trans ((C.disc_family ψ hψV).contour_family.2 m).2.2.1))
    exact ⟨hO,havoid,sourceStandardRootOmittedProduct_analyticOnNhd_spectral hp hp1 m V hP ψ hψV⟩
  refine ⟨U,δ,ε,hφU,hbase,⟨C,hrρ,hρR,⟨hU,hUV,hδ,hε,
    (fun ψ hψ => (hcoords ψ hψ).1),(fun ψ hψ => (hcoords ψ hψ).2.1),
    (fun ψ hψ => ⟨(hcoords ψ hψ).2.2.1,(hcoords ψ hψ).2.2.2.1⟩),
    (fun ψ hψ => (hcoords ψ hψ).2.2.2.2)⟩,hdata,?_⟩⟩
  intro ψ hψ
  exact ((hε ψ hψ).sub analyticAt_const).add
    (C.analyticAt_etaRemainderCauchyCandidate ρ hrρ hρR ψ (hUV hψ) (hμ ψ (hUV hψ)))

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
