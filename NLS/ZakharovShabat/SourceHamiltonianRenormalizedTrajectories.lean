import NLS.ZakharovShabat.SourceRenormalizedSourceTrajectoryAnalytic
import NLS.ZakharovShabat.SourceHamiltonianRenormalizedFlow
import NLS.ZakharovShabat.SourceHamiltonianTrajectories

/-! # Analytic compact-time trajectories with the physical time orientation

Time reflection is a bounded linear operation on the trajectory space.
Consequently the actual Hamiltonian-oriented renormalized source trajectories
retain analytic dependence on initial data in the uniform source norm.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

namespace SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {V B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual Hamiltonian-oriented trajectory on a compact time interval. -/
def hamiltonianRenormalizedSourceTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (hp2 : p ≤ 2) (T : ℝ) (φ : realTypeSourceSubmodule p) :
    C(Icc (-T) T,realTypeSourceSubmodule p) :=
  (A.renormalizedSourceTrajectoryOn hs hP hr D hp2 T φ).comp (hamiltonianTimeReflection T)

@[simp] theorem hamiltonianRenormalizedSourceTrajectoryOn_apply (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (hp2 : p ≤ 2) (T : ℝ) (φ : realTypeSourceSubmodule p) (time : Icc (-T) T) :
    A.hamiltonianRenormalizedSourceTrajectoryOn hs hP hr D hp2 T φ time =
      A.hamiltonianRenormalizedSourceFlow D hp2 φ time.val := rfl

/-- Real analytic dependence on initial data holds in the full uniform
trajectory norm, with the physical Hamiltonian time orientation. -/
theorem analytic_hamiltonianRenormalizedSourceTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (hp2 : p ≤ 2) (T : ℝ) :
    AnalyticOnNhd ℝ (A.hamiltonianRenormalizedSourceTrajectoryOn hs hP hr D hp2 T) univ := by
  intro φ _
  exact ((ContinuousMap.compCLM ℝ (realTypeSourceSubmodule p) (hamiltonianTimeReflection T)).analyticAt _).comp
    (A.analytic_renormalizedSourceTrajectoryOn hs hP hr D hp2 T φ (mem_univ _))

/-- Uniform source-norm continuity of the actual compact-time paths. -/
theorem continuous_hamiltonianRenormalizedSourceTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (hp2 : p ≤ 2) (T : ℝ) :
    Continuous (A.hamiltonianRenormalizedSourceTrajectoryOn hs hP hr D hp2 T) :=
  (A.analytic_hamiltonianRenormalizedSourceTrajectoryOn hs hP hr D hp2 T).continuous

/-- Every convergent family of initial sources gives convergence of entire
compact-time trajectories in the original source norm. -/
theorem tendsto_hamiltonianRenormalizedSourceTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (hp2 : p ≤ 2) (T : ℝ) {ι : Type*} {l : Filter ι}
    (φ : realTypeSourceSubmodule p) (ψ : ι → realTypeSourceSubmodule p)
    (hψ : Tendsto ψ l (𝓝 φ)) :
    Tendsto (fun j => A.hamiltonianRenormalizedSourceTrajectoryOn hs hP hr D hp2 T (ψ j)) l
      (𝓝 (A.hamiltonianRenormalizedSourceTrajectoryOn hs hP hr D hp2 T φ)) :=
  (A.continuous_hamiltonianRenormalizedSourceTrajectoryOn hs hP hr D hp2 T).continuousAt.tendsto.comp hψ

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
