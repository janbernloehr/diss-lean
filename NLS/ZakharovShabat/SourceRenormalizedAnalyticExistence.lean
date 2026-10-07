import NLS.ZakharovShabat.SourceRenormalizedFlowAnalytic

/-! # Constructed analytic renormalized dynamics

The actual spectral atlas and Birkhoff family are constructed together
with analytic compact-time coordinate trajectories and analytic fixed-time
source homeomorphisms. The result leaves no spectral or inverse-map
existence assumptions to the caller.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Construct the actual analytic coordinate trajectories and the bi-analytic
fixed-time source homeomorphisms in the globally invertible exponent range. -/
theorem exists_analytic_renormalizedDynamics (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W P : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ hs : SourcePsiSquaredGapComplexExtension hp hp1 P s,
    ∃ hP : IsOpen P, ∃ hr : realTypeSourceLocus p ⊆ P,
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
      (∀ T : ℝ, AnalyticOnNhd ℝ (A.renormalizedPhaseTrajectoryOn hs hP hr D T) univ) ∧
      (∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧
        (∀ T : ℝ, AnalyticOnNhd ℂ (A.complexPhaseTrajectoryOn t T) U) ∧
        ∀ T : ℝ, ∀ φ : realTypeSourceSubmodule p,
          A.complexPhaseTrajectoryOn t T φ.val = A.renormalizedPhaseTrajectoryOn hs hP hr D T φ) ∧
      ∀ hp2 : p ≤ 2, ∀ τ : ℝ,
        AnalyticOnNhd ℝ (A.renormalizedSourceHomeomorph hs hP hr D hp2 τ) univ ∧
          AnalyticOnNhd ℝ (A.renormalizedSourceHomeomorph hs hP hr D hp2 τ).symm univ := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨W₀,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨W,P,s,A,hs,hP,hr,W₀,B,X,t,D,
    A.analytic_renormalizedPhaseTrajectoryOn hs hP hr D,
    A.exists_analytic_complexPhaseTrajectoryOn hs hP hr D,
    A.renormalizedSourceHomeomorph_analytic hs hP hr D⟩

end NLS.ZakharovShabat
