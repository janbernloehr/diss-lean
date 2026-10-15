import NLS.ZakharovShabat.SourceSection22Global

/-! # Constructed original Section 22 phase and global solution data

One original family supplies the full complex trajectory neighborhood,
analytic dependence on its actual coordinate image, and both global
physical solution families in the surjective exponent range.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Construct the original phase package and global physical solutions before
choosing a source, index, or compact time horizon. Higher-exponent source
inversion and the nonextension assertions are separate subsequent results. -/
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

end NLS.ZakharovShabat
