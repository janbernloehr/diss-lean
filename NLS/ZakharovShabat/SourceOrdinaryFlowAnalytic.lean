import NLS.ZakharovShabat.SourceOrdinarySourceTrajectoryAnalytic

/-! # Bi-analytic ordinary NLS time maps

Evaluation of compact-time analytic trajectories gives analytic flow maps
at every fixed time. Negative time supplies their analytic inverses.
Initial Birkhoff coordinates also parameterize full paths analytically.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Analytic dependence of a coordinate state at any fixed real time. -/
theorem analytic_ordinaryPhaseTrajectory (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (τ : ℝ) : AnalyticOnNhd ℝ (fun φ => A.ordinaryPhaseTrajectory t hp2 φ τ) univ := by
  let τ₀ : Icc (-|τ|) |τ| := ⟨τ,neg_abs_le τ,le_abs_self τ⟩
  intro φ _
  have h := ((ContinuousMap.evalCLM ℝ τ₀).analyticAt _).comp
    (A.analytic_ordinaryPhaseTrajectoryOn hs hP hr D hp2 |τ| φ (mem_univ _))
  simpa only [Function.comp_def,ContinuousMap.evalCLM_apply,ordinaryPhaseTrajectoryOn,
    ContinuousMap.coe_mk,τ₀] using! h

/-- The actual nonlinear source map is real analytic at every fixed time. -/
theorem analytic_ordinarySourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (τ : ℝ) :
    AnalyticOnNhd ℝ (fun φ => A.ordinarySourceFlow D hp2 φ τ) univ := by
  intro φ _
  exact (D.realHomeomorph_symm_analytic hp2 _ (mem_univ _)).comp
    (((Birkhoff.decodeReal (p := p)).analyticAt _).comp
      (A.analytic_ordinaryPhaseTrajectory hs hP hr D hp2 τ φ (mem_univ _)))

/-- The flow homeomorphism and its negative-time inverse are both real analytic. -/
theorem ordinarySourceHomeomorph_analytic (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (τ : ℝ) :
    AnalyticOnNhd ℝ (A.ordinarySourceHomeomorph hs hP hr D hp2 τ) univ ∧
      AnalyticOnNhd ℝ (A.ordinarySourceHomeomorph hs hP hr D hp2 τ).symm univ :=
  ⟨A.analytic_ordinarySourceFlow hs hP hr D hp2 τ,
    A.analytic_ordinarySourceFlow hs hP hr D hp2 (-τ)⟩

/-- Analytic compact-time coordinate trajectories with real Birkhoff coordinates as initial data. -/
theorem analytic_ordinaryPhaseTrajectoryOn_coordinates
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (T : ℝ) :
    AnalyticOnNhd ℝ (fun z => A.ordinaryPhaseTrajectoryOn hs hP hr D hp2 T
      ((D.realHomeomorph hp2).symm z)) univ := by
  intro z _
  exact (A.analytic_ordinaryPhaseTrajectoryOn hs hP hr D hp2 T _ (mem_univ _)).comp
    (D.realHomeomorph_symm_analytic hp2 z (mem_univ _))

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
