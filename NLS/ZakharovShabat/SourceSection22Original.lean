import NLS.ZakharovShabat.SourceSection22Higher
import NLS.ZakharovShabat.SourceSection22Nonextension
import NLS.ZakharovShabat.SourceSection22Coordinates

/-! # Constructed original Section 22 phase and global solution data

One original family supplies the full complex trajectory neighborhood,
analytic dependence on its actual coordinate image, and both global
physical solution families in the surjective exponent range, local and
small-data global solutions above two, and the full phase characterization.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Construct the original phase package and global physical solutions before
choosing a source, index, or compact time horizon. The stronger constructor
below adds higher-exponent solutions and their full characterization. -/
theorem sourceSection22_original_flows (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s,
    ∃ D : SourceSection17OriginalData hp hp1 W₀ W V s,
    ∃ Wa : Set (CoeffPair p), ∃ A : SourceAbelianMomentAtlas hp hp1 Wa s,
    ∃ B U : Set (CoeffPair p), ∃ _Q : SourceSection20Data D A B U,
      (∀ T : ℝ, AnalyticOnNhd ℂ (A.hamiltonianComplexPhaseTrajectoryOn T) U) ∧
      (∀ T : ℝ, AnalyticOnNhd ℝ (A.hamiltonianCoordinateTrajectoryOn D.complex T)
        (range (sourceRealBirkhoffMap hp hp1 s))) ∧
      ∀ hp2 : p ≤ 2,
        (∀ φ : realTypeSourceSubmodule p,
          IsRenormalizedNLSSolutionOn univ φ (A.hamiltonianRenormalizedSourceFlow D.complex hp2 φ) ∧
          IsOrdinaryNLSSolutionOn univ φ (A.hamiltonianOrdinarySourceFlow D.complex hp2 φ)) ∧
        IsGloballyAnalyticallyWellposedOn (fun f : SmoothNLSData => f.renormalizedSource p) univ ∧
        IsGloballyAnalyticallyWellposedOn (fun f : SmoothNLSData => f.ordinarySource p) univ := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original hp hp1
  exact ⟨W₀,W,V,s,D,Wa,A,B,U,Q,Q.hamiltonian_phase_analytic,Q.hamiltonian_coordinate_analytic,
    fun hp2 => ⟨Q.global_physical_solutions hp2,Q.global_analytic_wellposedness hp2⟩⟩

/-- One constructed original family supports the complete Section 22 existence
and characterization results. Coordinate and source nonextension are the methods
`coordinate_nonextension_fst`, `coordinate_nonextension_snd`, and
`smooth_source_nonextension` of the same retained Q. -/
theorem sourceSection22_original (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s,
    ∃ D : SourceSection17OriginalData hp hp1 W₀ W V s,
    ∃ Wa : Set (CoeffPair p), ∃ A : SourceAbelianMomentAtlas hp hp1 Wa s,
    ∃ B U : Set (CoeffPair p), ∃ _Q : SourceSection20Data D A B U,
      (∀ T : ℝ, AnalyticOnNhd ℂ (A.hamiltonianComplexPhaseTrajectoryOn T) U) ∧
      (∀ T : ℝ, AnalyticOnNhd ℝ (A.hamiltonianCoordinateTrajectoryOn D.complex T)
        (range (sourceRealBirkhoffMap hp hp1 s))) ∧
      IsLocallyAnalyticallyWellposed (fun f : SmoothNLSData => f.renormalizedSource p) ∧
      (∀ _hp2 : p ≤ 2,
        IsGloballyAnalyticallyWellposedOn (fun f : SmoothNLSData => f.renormalizedSource p) univ ∧
        IsGloballyAnalyticallyWellposedOn (fun f : SmoothNLSData => f.ordinarySource p) univ) ∧
      (∀ _h2p : 2 ≤ p, ∃ V' : Set (realTypeSourceSubmodule p),
        (0 : realTypeSourceSubmodule p) ∈ V' ∧ (∃ r > 0, Metric.ball 0 r ⊆ V') ∧
        (∀ φ ∈ V', ∀ τ : ℝ, (-τ,φ) ∈ A.renormalizedImageDomain s) ∧
        (∀ φ ∈ V', IsRenormalizedNLSSolutionOn univ φ
          (A.hamiltonianRenormalizedImageFlow D.complex φ)) ∧
        IsGloballyAnalyticallyWellposedOn (fun f : SmoothNLSData => f.renormalizedSource p) V') ∧
      ∀ T : ℝ, ∀ _hT : 0 ≤ T, ∀ φ : realTypeSourceSubmodule p,
        ∀ γ : ℝ → realTypeSourceSubmodule p,
        IsRenormalizedNLSSolutionOn (Icc (-T) T) φ γ ↔
          ContinuousOn γ (Icc (-T) T) ∧
          ∀ τ ∈ Icc (-T) T, sourceComplexBirkhoffMap hp hp1 s (γ τ).val =
            Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency φ) τ
              (sourceComplexBirkhoffMap hp hp1 s φ.val) := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original hp hp1
  refine ⟨W₀,W,V,s,D,Wa,A,B,U,Q,Q.hamiltonian_phase_analytic,Q.hamiltonian_coordinate_analytic,
    Q.local_analytic_wellposedness,Q.global_analytic_wellposedness,?_,Q.remark22_3⟩
  intro h2p
  obtain ⟨V',_,hz,hball,hvalid,_,hsol,_,_,_,hwp⟩ := Q.small_global_physical_solutions h2p
  exact ⟨V',hz,hball,fun φ hφ τ => hvalid φ hφ (-τ),hsol,hwp⟩

end NLS.ZakharovShabat
