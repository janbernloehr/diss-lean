import NLS.ComplexAnalysis.ContinuousMapAnalyticInverse
import NLS.ZakharovShabat.SourceRenormalizedFlowAnalytic
import NLS.ZakharovShabat.SourceRealTypeProjection

/-! # Analytic dependence of complete source trajectories

The actual Birkhoff map acts analytically on compact trajectory spaces.
Its pointwise Jacobians are invertible along every real source path, so
the function-space inverse theorem upgrades the known continuous source
trajectory lift to a real analytic lift. Projection to the original closed
real source form retains the exact trajectory, with its uniform norm.
-/
noncomputable section
open Set Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Forget only the real-form subtype on an actual source trajectory. -/
def ambientSourceTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (T : ℝ) (φ : realTypeSourceSubmodule p) : C(Icc (-T) T,CoeffPair p) :=
  ((realTypeSourceSubmodule p).subtypeL.compLeftContinuous ℝ (Icc (-T) T))
    (A.renormalizedSourceTrajectoryOn hs hP hr D hp2 T φ)

/-- The compact-time coordinate curve in the original rectangular coordinates. -/
def rectangularPhaseTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (T : ℝ) (φ : realTypeSourceSubmodule p) : C(Icc (-T) T,Coeff p × Coeff p) :=
  ((Birkhoff.rectangularToComplex (p := p)).symm.toContinuousLinearMap.compLeftContinuous ℂ (Icc (-T) T))
    (A.renormalizedPhaseTrajectoryOn hs hP hr D T φ)

/-- Applying the actual Birkhoff map pointwise gives exactly the rectangular trajectory. -/
theorem superposition_ambientSourceTrajectoryOn
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (T : ℝ) (φ : realTypeSourceSubmodule p) :
    superposition (sourceBirkhoffMap hp hp1 t) (A.ambientSourceTrajectoryOn hs hP hr D hp2 T φ) =
      A.rectangularPhaseTrajectoryOn hs hP hr D T φ := by
  apply ContinuousMap.ext
  intro τ
  rw [superposition_apply D.analytic.continuousOn (by
    rintro _ ⟨σ,rfl⟩
    exact D.real_subset (A.renormalizedSourceFlow D hp2 φ σ.val).property)]
  change sourceBirkhoffMap hp hp1 t (A.renormalizedSourceFlow D hp2 φ τ.val).val =
    Birkhoff.rectangularToComplex.symm (A.renormalizedPhaseTrajectory t φ τ.val)
  have h := congrArg (Birkhoff.rectangularToComplex (p := p)).symm
    (A.complex_map_renormalizedSourceFlow D hp2 φ τ.val)
  simpa only [sourceComplexBirkhoffMap,ContinuousLinearEquiv.symm_apply_apply] using! h

/-- The ambient source-valued compact-time trajectory is real analytic. -/
theorem analytic_ambientSourceTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (T : ℝ) :
    AnalyticOnNhd ℝ (A.ambientSourceTrajectoryOn hs hP hr D hp2 T) univ := by
  intro φ _
  apply analyticAt_real_lift_of_superposition D.source_open D.analytic
    (A.ambientSourceTrajectoryOn hs hP hr D hp2 T) φ
  · exact (((realTypeSourceSubmodule p).subtypeL.compLeftContinuous ℝ (Icc (-T) T)).continuous.comp
      (A.continuous_renormalizedSourceTrajectoryOn hs hP hr D hp2 T)).continuousAt
  · rintro _ ⟨τ,rfl⟩
    exact D.real_subset (A.renormalizedSourceFlow D hp2 φ τ.val).property
  · intro τ
    exact ⟨D.jacobianEquivAll (A.renormalizedSourceFlow D hp2 φ τ.val),rfl⟩
  · have hrect :=
      ((((Birkhoff.rectangularToComplex (p := p)).symm.toContinuousLinearMap.compLeftContinuous ℂ
        (Icc (-T) T)).restrictScalars ℝ).analyticAt _).comp
        (A.analytic_renormalizedPhaseTrajectoryOn hs hP hr D T φ (mem_univ _))
    simpa only [A.superposition_ambientSourceTrajectoryOn,rectangularPhaseTrajectoryOn,
      Function.comp_def] using! hrect

/-- Analytic dependence on initial data in the full source trajectory norm on every [-T,T]. -/
theorem analytic_renormalizedSourceTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (T : ℝ) :
    AnalyticOnNhd ℝ (A.renormalizedSourceTrajectoryOn hs hP hr D hp2 T) univ := by
  have he (φ : realTypeSourceSubmodule p) :
      ((sourceRealTypeProjection hp).compLeftContinuous ℝ (Icc (-T) T))
        (A.ambientSourceTrajectoryOn hs hP hr D hp2 T φ) =
      A.renormalizedSourceTrajectoryOn hs hP hr D hp2 T φ := by
    apply ContinuousMap.ext
    intro τ
    exact sourceRealTypeProjection_subtype hp (A.renormalizedSourceFlow D hp2 φ τ.val)
  intro φ _
  have h := (((sourceRealTypeProjection hp).compLeftContinuous ℝ (Icc (-T) T)).analyticAt _).comp
    (A.analytic_ambientSourceTrajectoryOn hs hP hr D hp2 T φ (mem_univ _))
  simpa only [Function.comp_def,he] using! h

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
