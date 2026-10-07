import NLS.ZakharovShabat.SourceRenormalizedPhaseAnalytic

/-! # Analytic fixed-time renormalized source maps

Evaluation of the analytic compact-time coordinate trajectory is analytic.
Composing with the actual global real Birkhoff inverse proves analyticity
of every fixed-time source map for 1 < p ≤ 2. Its negative-time inverse is
analytic as well. Analyticity of the complete source-valued trajectory map
requires a further result about composition on continuous function spaces.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Analytic dependence of a coordinate state at any fixed real time. -/
theorem analytic_renormalizedPhaseTrajectory (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (τ : ℝ) : AnalyticOnNhd ℝ (fun φ => A.renormalizedPhaseTrajectory t φ τ) univ := by
  let τ₀ : Icc (-|τ|) |τ| := ⟨τ,neg_abs_le τ,le_abs_self τ⟩
  intro φ _
  have h := ((ContinuousMap.evalCLM ℝ τ₀).analyticAt _).comp
    (A.analytic_renormalizedPhaseTrajectoryOn hs hP hr D |τ| φ (mem_univ _))
  simpa only [Function.comp_def,ContinuousMap.evalCLM_apply,renormalizedPhaseTrajectoryOn,
    ContinuousMap.coe_mk,τ₀] using! h

/-- The actual nonlinear source map is real analytic at every fixed time. -/
theorem analytic_renormalizedSourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (τ : ℝ) :
    AnalyticOnNhd ℝ (fun φ => A.renormalizedSourceFlow D hp2 φ τ) univ := by
  intro φ _
  exact (D.realHomeomorph_symm_analytic hp2 _ (mem_univ _)).comp
    (((Birkhoff.decodeReal (p := p)).analyticAt _).comp
      (A.analytic_renormalizedPhaseTrajectory hs hP hr D τ φ (mem_univ _)))

/-- The flow homeomorphism and its negative-time inverse are both real analytic. -/
theorem renormalizedSourceHomeomorph_analytic (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (τ : ℝ) :
    AnalyticOnNhd ℝ (A.renormalizedSourceHomeomorph hs hP hr D hp2 τ) univ ∧
      AnalyticOnNhd ℝ (A.renormalizedSourceHomeomorph hs hP hr D hp2 τ).symm univ :=
  ⟨A.analytic_renormalizedSourceFlow hs hP hr D hp2 τ,
    A.analytic_renormalizedSourceFlow hs hP hr D hp2 (-τ)⟩

/-- Analytic compact-time coordinate trajectories with real Birkhoff coordinates as initial data. -/
theorem analytic_renormalizedPhaseTrajectoryOn_coordinates
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (T : ℝ) :
    AnalyticOnNhd ℝ (fun z => A.renormalizedPhaseTrajectoryOn hs hP hr D T
      ((D.realHomeomorph hp2).symm z)) univ := by
  intro z _
  exact (A.analytic_renormalizedPhaseTrajectoryOn hs hP hr D T _ (mem_univ _)).comp
    (D.realHomeomorph_symm_analytic hp2 z (mem_univ _))

/-- At every finite exponent, inverse charts give analytic dependence on the
initial real Birkhoff coordinates, locally on the actual coordinate image. -/
theorem exists_analytic_coordinateTrajectory_germ
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (T : ℝ) (φ : realTypeSourceSubmodule p) :
    ∃ G : (RealCoeff p × RealCoeff p) → C(Icc (-T) T, Coeff p × Coeff p),
      AnalyticAt ℝ G (sourceRealBirkhoffMap hp hp1 t φ) ∧
      G (sourceRealBirkhoffMap hp hp1 t φ) = A.renormalizedPhaseTrajectoryOn hs hP hr D T φ ∧
      ∀ᶠ ψ in 𝓝 φ, G (sourceRealBirkhoffMap hp hp1 t ψ) =
        A.renormalizedPhaseTrajectoryOn hs hP hr D T ψ := by
  obtain ⟨g,hg,hg₀,hl,_,_⟩ := D.proposition17_1 φ
  refine ⟨fun z => A.renormalizedPhaseTrajectoryOn hs hP hr D T (g z),?_,?_,?_⟩
  · exact (A.analytic_renormalizedPhaseTrajectoryOn hs hP hr D T _ (mem_univ _)).comp hg
  · dsimp only
    rw [hg₀]
  · filter_upwards [hl] with ψ hψ
    rw [hψ]

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
