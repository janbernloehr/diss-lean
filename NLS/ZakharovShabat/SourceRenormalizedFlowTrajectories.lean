import NLS.ZakharovShabat.SourceRenormalizedFlow
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Continuous dependence in compact-time trajectory spaces

Joint continuity gives continuity into C([-T,T], E), whose topology is the
uniform norm topology. Thus convergence of real initial sources gives
uniform-in-time convergence of the actual coordinate trajectories at every
finite exponent, and of the lifted source trajectories when p ≤ 2.
This establishes continuous dependence, not the stronger analyticity claim.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Coordinate trajectories on any compact real time interval. -/
def renormalizedPhaseTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hrealP : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (T : ℝ) (φ : realTypeSourceSubmodule p) : C(Icc (-T) T, Coeff p × Coeff p) where
  toFun τ := A.renormalizedPhaseTrajectory t φ τ.val
  continuous_toFun := by
    simpa only [Function.comp_def] using!
      (A.continuous_renormalizedPhaseTrajectory hs hP hrealP D).comp
        (show Continuous (fun τ : Icc (-T) T => (τ.val,φ)) from
          continuous_subtype_val.prodMk continuous_const)

/-- Full-sequence continuous dependence, uniformly on each compact time interval. -/
theorem continuous_renormalizedPhaseTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hrealP : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (T : ℝ) : Continuous (A.renormalizedPhaseTrajectoryOn hs hP hrealP D T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  simpa only [Function.comp_def, Function.uncurry, renormalizedPhaseTrajectoryOn, ContinuousMap.coe_mk] using!
    (A.continuous_renormalizedPhaseTrajectory hs hP hrealP D).comp
      (show Continuous (fun x : realTypeSourceSubmodule p × Icc (-T) T => (x.2.val,x.1)) from
        (continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)

/-- Actual source trajectories on a compact time interval in the globally invertible range. -/
def renormalizedSourceTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hrealP : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (T : ℝ) (φ : realTypeSourceSubmodule p) :
    C(Icc (-T) T, realTypeSourceSubmodule p) where
  toFun τ := A.renormalizedSourceFlow D hp2 φ τ.val
  continuous_toFun := by
    simpa only [Function.comp_def] using!
      (A.continuous_renormalizedSourceFlow hs hP hrealP D hp2).comp
        (show Continuous (fun τ : Icc (-T) T => (τ.val,φ)) from
          continuous_subtype_val.prodMk continuous_const)

/-- The source trajectory map is continuous in the uniform source norm on every compact time interval. -/
theorem continuous_renormalizedSourceTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hrealP : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (T : ℝ) : Continuous (A.renormalizedSourceTrajectoryOn hs hP hrealP D hp2 T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  simpa only [Function.comp_def, Function.uncurry, renormalizedSourceTrajectoryOn, ContinuousMap.coe_mk] using!
    (A.continuous_renormalizedSourceFlow hs hP hrealP D hp2).comp
      (show Continuous (fun x : realTypeSourceSubmodule p × Icc (-T) T => (x.2.val,x.1)) from
        (continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)

/-- Convergent initial sources give uniformly convergent source trajectories on [-T,T]. -/
theorem tendstoUniformly_renormalizedSourceTrajectory (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hrealP : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (T : ℝ) {ι : Type*} {l : Filter ι}
    (φ : ι → realTypeSourceSubmodule p) (ψ : realTypeSourceSubmodule p)
    (hφ : Tendsto φ l (𝓝 ψ)) :
    TendstoUniformly (fun i (τ : Icc (-T) T) => A.renormalizedSourceFlow D hp2 (φ i) τ.val)
      (fun τ => A.renormalizedSourceFlow D hp2 ψ τ.val) l := by
  exact ContinuousMap.tendsto_iff_tendstoUniformly.mp
    ((A.continuous_renormalizedSourceTrajectoryOn hs hP hrealP D hp2 T).continuousAt.tendsto.comp hφ)

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
