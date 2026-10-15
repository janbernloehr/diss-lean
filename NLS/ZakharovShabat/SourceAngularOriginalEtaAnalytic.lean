import NLS.ZakharovShabat.SourceAngularOriginalEndpointIntegrals
import NLS.ZakharovShabat.SourceAngularOriginalAnnulus
import NLS.ZakharovShabat.SourceAngularEtaAnalyticPhase
import NLS.ZakharovShabat.SourceAngularCauchyReal

/-!
# Actual eta charts on the retained Section 12 domain

The original annuli and symmetric spectral data construct analytic eta
representatives without changing the source domain or normalized psi family.
The associated phase is nonzero and analytic at every complex open gap.
A constructed integrable endpoint path realizes that phase.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Original annuli construct local eta charts while retaining W and its disk family. -/
theorem eta_original_analytic_chart (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0) :
    ∃ V U : Set (CoeffPair p), ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ,
      ∃ r R : ℝ, ∃ z₀ : ℂ, ∃ ρ : ℝ, ∃ δ ε : CoeffPair p → ℂ,
        φ ∈ U ∧ U ⊆ W ∧
        δ φ = canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m/2 ∧
        SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε ∧
        ∃ C₀ : ℝ, SourceIsolatingNeighborhoods hp hp1 V (fun k => ball (c k) (T k)) C₀ := by
  obtain ⟨V,c,T,r,R,z₀,hφV,C,hD⟩ := H.angular_original_annulus_chart φ hφ m
  let ρ := (r+R)/2
  have hrρ : r < ρ := by dsimp [ρ]; linarith [C.inner_lt_outer]
  have hρR : ρ < R := by dsimp [ρ]; linarith [C.inner_lt_outer]
  let H2 := H.previous.previous.psi.previous.quotients.roots.roots.symmetric
  have hsym (ψ : CoeffPair p) (hψ : ψ ∈ V) (k : ℤ) :
      AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p => (canonicalPeriodicGap hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k)^2) ψ :=
    ⟨H2.midpoint k ψ (H.previous.previous.subset (C.source_subset hψ)),
      H2.squared_gap k ψ (H.previous.previous.subset (C.source_subset hψ))⟩
  obtain ⟨hO,hP⟩ := sourceStandardRootOmittedJointProduct_analyticOnNhd_of_symmetric hp hp1
    V C.source_open hsym m
  have hμ : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) V :=
    fun ψ hψ => (H2.simplicity.boundary ψ (H.previous.previous.subset (C.source_subset hψ)) .dirichlet m).1
  obtain ⟨U,δ,ε,hφU,hbase,E⟩ := C.exists_local_analytic_eta_chart ρ hrρ hρR φ hφV hgap
    (hsym φ hφV m).1 (hsym φ hφV m).2 hμ hO hP
  exact ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,E.angle.source_subset.trans C.source_subset,hbase,E,hD⟩

/-- The eta phase is analytic and nonzero on the open-gap part of the original domain. -/
theorem eta_original_phase_analytic (H : SourceLemma12_12Data hp hp1 W₀ W s) (m : ℤ) :
    IsOpen {ψ : CoeffPair p | ψ ∈ W ∧
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0} ∧
    AnalyticOnNhd ℂ (sourceAngularEtaAnalyticPhase hp hp1 m s)
      {ψ : CoeffPair p | ψ ∈ W ∧
        canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0} ∧
    ∀ ψ ∈ W, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0 →
      sourceAngularEtaAnalyticPhase hp hp1 m s ψ ≠ 0 := by
  refine ⟨?_,?_,?_⟩
  · apply isOpen_iff_mem_nhds.mpr
    intro φ hφ
    obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,hUW,_,E,_⟩ := H.eta_original_analytic_chart φ hφ.1 m hφ.2
    exact mem_of_superset (E.angle.source_open.mem_nhds hφU)
      (fun ψ hψ => ⟨hUW hψ,E.gap_ne_zero ψ hψ⟩)
  · intro φ hφ
    obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,_,_,E,_⟩ := H.eta_original_analytic_chart φ hφ.1 m hφ.2
    exact E.analyticOnNhd_phase φ hφU
  · intro φ hφ hgap
    obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,_,_,E,_⟩ := H.eta_original_analytic_chart φ hφ m hgap
    exact E.phase_ne_zero φ hφU

/-- The original beta values are real on the real-type locus, including collapsed gaps. -/
theorem beta_original_im_eq_zero (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) : (sourceAngularBeta hp hp1 n m s ψ).im = 0 := by
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m = 0
  · rw [sourceAngularBeta_eq_zero_of_real_collapsed_gap hp hp1 n m s ψ hreal
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)]
    rfl
  · obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hψU,_,_,E,_⟩ := H.eta_original_analytic_chart ψ hψ m hgap
    exact E.beta_im_eq_zero_of_realType H.angular_extension.toSourcePsiIsolatingComplexExtension
      ψ hψU hreal n hmn


/-- An actual normalized endpoint integral in an original disk realizes the eta chart phase. -/
theorem eta_original_exists_phase_integral (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0) :
    ∃ P : SourceCriticalRootPeriodCircle hp hp1 ψ m,
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius ∧
      ∃ Q : ℂ × CoeffPair p → ℂ,
        ∃ γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m),
          SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ ∧
          ContDiffOn ℝ 1 γ.extend (Icc 0 1) ∧
          Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
            sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ∧
          CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ ∧
          CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) γ ∧
          Complex.exp (2*Complex.I*sourceAngularPathIntegral m s Q ψ γ) =
            sourceAngularEtaAnalyticPhase hp hp1 m s ψ := by
  obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hψU,_,_,E,C₀,hD⟩ := H.eta_original_analytic_chart ψ hψ m hgap
  have hψV := E.angle.source_subset hψU
  have hc : ((c m).re:ℂ) = c m := by
    simpa only [(E.annulus.disc_family ψ hψV).contour_family.1 m,Complex.ofReal_zero,zero_mul,add_zero]
      using Complex.re_add_im (c m)
  let P := hD.periodCircle ψ hψV m (c m).re (T m)
    ((E.annulus.disc_family ψ hψV).contour_family.2 m).1 (by rw [hc])
  have hrT : r < T m := E.annulus.inner_lt_outer.trans E.annulus.outer_lt_assigned
  let P' : SourceCriticalRootPeriodCircle hp hp1 ψ m := {
    center := (c m).re
    radius := r
    radius_pos := E.annulus.inner_pos
    gap := by rw [hc]; exact E.annulus.gap_enclosed ψ hψV
    other := by
      intro j hj w hw
      rcases P.other j hj w hw with hl | hr
      · left
        change w.re < (c m).re-T m at hl
        linarith
      · right
        change (c m).re+T m < w.re at hr
        linarith }
  have hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P'.center:ℂ) P'.radius := by
    change _ ∈ ball ((c m).re:ℂ) r
    rw [hc]
    exact E.annulus.terminal_enclosed ψ hψV
  obtain ⟨Q,γ,hQ,hγ,hnorm,_,hint⟩ := H.original_dirichlet_integral_path ψ hψ m P' hμ
  have hgap' : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    intro he
    apply hgap
    simp only [canonicalPeriodicGap,he,sub_self]
  obtain ⟨hi,hm⟩ := hint hgap'
  have hQinner : SourceAngularAdmissiblePathRootData hp hp1 m ψ (c m) r Q γ := by
    simpa only [P',hc] using hQ
  have hQouter : SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ := by
    refine ⟨hQ.continuous_root,hQ.square_root,?_⟩
    intro t ht
    exact ⟨(ball_subset_ball hrT.le) (hQ.interior t ht).1,(hQ.interior t ht).2⟩
  refine ⟨P,(ball_subset_ball hrT.le) hμ,Q,γ,hQouter,hγ,hnorm,hi,hm,?_⟩
  exact E.exp_two_I_admissible_pathIntegral_eq_phase ψ hψU (by simp) Q γ hQinner
    (fun _ => hnorm) hγ hi hm

end SourceLemma12_12Data
end NLS.ZakharovShabat
