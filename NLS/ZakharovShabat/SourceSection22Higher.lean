import NLS.ZakharovShabat.SourceSection22Characterization
import NLS.ZakharovShabat.HigherExponentAnalyticNLSSolutions
/-! # Original higher-exponent local and small-data global solutions

Every inverse and frequency belongs to the retained original family.
Source inversion keeps its explicit trajectory-image condition.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- Corollary 22.2(ii): one neighborhood and positive time for every original source. -/
theorem local_physical_solutions (h2p : 2 ≤ p) (φ : realTypeSourceSubmodule p) :
    ∃ T > 0, ∃ V' : Set (realTypeSourceSubmodule p), IsOpen V' ∧ φ ∈ V' ∧
      V' ⊆ A.renormalizedTrajectoryDomain s T ∧
      (∀ ψ ∈ V', IsRenormalizedNLSSolutionOn (Icc (-T) T) ψ
        (A.hamiltonianRenormalizedImageFlow D.complex ψ)) ∧
      AnalyticOnNhd ℝ (A.hamiltonianRenormalizedImageTrajectoryOn D.complex T) V' ∧
      ∀ ψ ∈ V', ∀ τ : Icc (-T) T,
        A.hamiltonianRenormalizedImageTrajectoryOn D.complex T ψ τ =
          A.hamiltonianRenormalizedImageFlow D.complex ψ τ.val := by
  obtain ⟨T,hT,V',hV,hφ,hsub,_⟩ := A.exists_local_analytic_renormalizedTrajectories
    Q.roots D.roots_open D.roots_real_subset D.complex φ
  exact ⟨T,hT,V',hV,hφ,hsub,
    fun ψ hψ => A.renormalizedImageFlow_isSolution Q.roots D.roots_open D.roots_real_subset
      D.complex h2p ψ T hT.le (hsub hψ),
    (A.analytic_hamiltonianRenormalizedImageTrajectoryOn Q.roots D.roots_open
      D.roots_real_subset D.complex T).mono hsub,
    fun ψ hψ τ => A.hamiltonianRenormalizedImageTrajectoryOn_apply Q.roots D.roots_open
      D.roots_real_subset D.complex T ψ (hsub hψ) τ⟩

/-- One invariant open neighborhood of zero has global physical solutions and
analytic trajectories for every compact time horizon. It contains a positive source-norm ball. -/
theorem small_global_physical_solutions (h2p : 2 ≤ p) :
    ∃ V' : Set (realTypeSourceSubmodule p), IsOpen V' ∧
      (0 : realTypeSourceSubmodule p) ∈ V' ∧
      (∃ r > 0, Metric.ball 0 r ⊆ V') ∧
      (∀ φ ∈ V', ∀ τ : ℝ, (τ,φ) ∈ A.renormalizedImageDomain s) ∧
      (∀ φ ∈ V', ∀ τ : ℝ, A.hamiltonianRenormalizedImageFlow D.complex φ τ ∈ V') ∧
      (∀ φ ∈ V', IsRenormalizedNLSSolutionOn univ φ
        (A.hamiltonianRenormalizedImageFlow D.complex φ)) ∧
      (∀ T : ℝ, AnalyticOnNhd ℝ (A.hamiltonianRenormalizedImageTrajectoryOn D.complex T) V') ∧
      ContinuousOn (fun x : ℝ × realTypeSourceSubmodule p =>
        A.hamiltonianRenormalizedImageFlow D.complex x.2 x.1) (univ ×ˢ V') ∧
      (∀ φ ∈ V', ∀ τ σ : ℝ,
        A.hamiltonianRenormalizedImageFlow D.complex
          (A.hamiltonianRenormalizedImageFlow D.complex φ σ) τ =
            A.hamiltonianRenormalizedImageFlow D.complex φ (τ+σ)) ∧
      IsGloballyAnalyticallyWellposedOn (fun f : SmoothNLSData => f.renormalizedSource p) V' := by
  obtain ⟨V',hV,hzero,hball,hvalid,hinv⟩ := A.exists_invariant_small_renormalizedFlow D.complex
  have hsol := A.renormalizedImageFlow_isGlobalSolution Q.roots D.roots_open
    D.roots_real_subset D.complex h2p V' hvalid
  have hsub (T : ℝ) : V' ⊆ A.renormalizedTrajectoryDomain s T :=
    fun φ hφ τ => hvalid φ hφ τ.val
  have ha (T : ℝ) := (A.analytic_hamiltonianRenormalizedImageTrajectoryOn Q.roots
    D.roots_open D.roots_real_subset D.complex T).mono (hsub T)
  refine ⟨V',hV,hzero,hball,hvalid,fun φ hφ τ => hinv φ hφ (-τ),hsol,ha,
    A.continuousOn_hamiltonianRenormalizedImageFlow Q.roots D.roots_open
      D.roots_real_subset D.complex V' hvalid,
    fun φ hφ τ σ => A.hamiltonianRenormalizedImageFlow_add
      Q.roots.toSourcePsiIsolatingComplexExtension D.complex φ τ σ (hvalid φ hφ (-σ)),
    hV,A.hamiltonianRenormalizedImageFlow D.complex,hsol,?_⟩
  intro T _
  exact ⟨A.hamiltonianRenormalizedImageTrajectoryOn D.complex T,ha T,
    fun φ hφ τ => A.hamiltonianRenormalizedImageTrajectoryOn_apply Q.roots D.roots_open
      D.roots_real_subset D.complex T φ (hsub T hφ) τ⟩
/-- The original family proves local analytic wellposedness at every finite p > 1. -/
theorem local_analytic_wellposedness :
    IsLocallyAnalyticallyWellposed (fun f : SmoothNLSData => f.renormalizedSource p) := by
  rcases le_total p 2 with hp2 | h2p
  · exact (Q.global_analytic_wellposedness hp2).1.local
  · intro φ
    obtain ⟨T,hT,V',hV,hφ,_,hsol,ha,he⟩ := Q.local_physical_solutions h2p φ
    exact ⟨T,hT,V',hV,hφ,A.hamiltonianRenormalizedImageFlow D.complex,hsol,
      A.hamiltonianRenormalizedImageTrajectoryOn D.complex T,ha,he⟩

end NLS.ZakharovShabat.SourceSection20Data
