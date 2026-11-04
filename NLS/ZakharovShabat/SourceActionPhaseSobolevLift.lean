import NLS.ZakharovShabat.SourceSobolevPhaseFlow
import NLS.ZakharovShabat.SourceActionPhaseGlobalODE
import NLS.ZakharovShabat.SourceWeightedRealSourceInclusion

/-! # Arbitrary action-frequency lifts in every native Sobolev norm

Only coordinatewise continuity of the actual real frequencies is required.
The weighted lift forgets to the same original source image flow. Uniform
compact-time continuity is in each full native weighted norm.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceActionFrequency
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B X : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual image lift with its complete original Sobolev regularity. -/
def sobolevImageFlow (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) (time : ℝ) :
    weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ) :=
  D.weightedSourcePhaseFlow hp2 σ hσ
    (F.frequency (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a)) a time

/-- Forgetting the stronger norm recovers precisely the actual source flow. -/
theorem originalWeightedRealSource_sobolevImageFlow (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) (time : ℝ) :
    originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ)
      (F.sobolevImageFlow D hp2 σ hσ a time) =
    F.imageFlow D (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a) time := by
  rw [F.imageFlow_eq_globalInverse D hp2]
  exact D.originalWeightedRealSource_weightedSourcePhaseFlow hp2 σ hσ _ a time

@[simp] theorem sobolevImageFlow_zero (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) :
    F.sobolevImageFlow D hp2 σ hσ a 0 = a :=
  D.weightedSourcePhaseFlow_zero hp2 σ hσ _ a

/-- Actual weighted source trajectories depend jointly continuously on time
and initial data; a bounded frequency sequence is not required. -/
theorem continuous_sobolevImageFlow (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) :
    Continuous (fun x : ℝ × weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ) =>
      F.sobolevImageFlow D hp2 σ hσ x.2 x.1) := by
  let w := sourceSobolevSpectralWeight σ hσ
  let E := weightedRealSourceSubmodule (p := p) w
  let R := Birkhoff.weightedRealCoordinates (p := p) (sourceFrequencyWeight w)
  have hω (n : ℤ) : Continuous (fun a : E => F.frequency (originalWeightedRealSource w a) n) :=
    (F.continuous n).comp (continuous_originalWeightedRealSource w)
  have hz : Continuous (fun a : E => Birkhoff.encodeReal (R (D.originalWeightedRealMap w a))) :=
    Birkhoff.encodeReal.continuous.comp (R.continuous.comp
      (continuousOn_univ.mp (D.originalWeightedRealMap_analytic w).continuousOn))
  have hc := (Birkhoff.continuous_phaseFlow_family hp _ _ hω hz).comp
    (continuous_fst.neg.prodMk continuous_snd)
  exact (D.originalWeightedRealSobolevHomeomorph hp2 σ hσ).symm.continuous.comp
    (R.symm.continuous.comp (Birkhoff.decodeReal.continuous.comp hc))

/-- The actual Sobolev source path on a complete compact time interval. -/
def sobolevTrajectoryOn (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) (T : ℝ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) :
    C(Icc (-T) T,weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) where
  toFun time := F.sobolevImageFlow D hp2 σ hσ a time.val
  continuous_toFun := (F.continuous_sobolevImageFlow D hp2 σ hσ).comp
    (f := fun time : Icc (-T) T => (time.val,a))
    (continuous_subtype_val.prodMk continuous_const)

/-- Initial-data continuity in the full uniform Sobolev trajectory norm. -/
theorem continuous_sobolevTrajectoryOn (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) (T : ℝ) :
    Continuous (F.sobolevTrajectoryOn D hp2 σ hσ T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (F.continuous_sobolevImageFlow D hp2 σ hσ).comp
    (f := fun x : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ) × Icc (-T) T =>
      (x.2.val,x.1))
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)

/-- Every convergent family converges in the full uniform native Sobolev
trajectory norm, for an arbitrary action-invariant frequency family. -/
theorem tendstoUniformly_sobolevImageFlow (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) (T : ℝ)
    {ι : Type*} {l : Filter ι}
    (a : ι → weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ))
    (b : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ))
    (ha : Tendsto a l (𝓝 b)) :
    TendstoUniformly (fun i (time : Icc (-T) T) => F.sobolevImageFlow D hp2 σ hσ (a i) time.val)
      (fun time => F.sobolevImageFlow D hp2 σ hσ b time.val) l :=
  ContinuousMap.tendsto_iff_tendstoUniformly.mp
    (((F.continuous_sobolevTrajectoryOn D hp2 σ hσ T).continuousAt.tendsto).comp ha)

end NLS.ZakharovShabat.SourceActionFrequency
