import NLS.ZakharovShabat.SourceActionPhaseLocalFlow
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Uniform-norm continuous source trajectories for action phase families

Admissible initial sources form an open set for each compact time interval.
The actual inverse lift is continuous into C([-T,T],source) in its uniform
norm, at every finite exponent, including exponents above two.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceActionFrequency
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The full Hamiltonian coordinate path on a compact time interval. -/
def phaseTrajectoryOn (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (T : ℝ)
    (φ : realTypeSourceSubmodule p) : C(Icc (-T) T,Coeff p × Coeff p) where
  toFun τ := F.phaseTrajectory D φ τ.val
  continuous_toFun := by
    simpa only [Function.comp_def] using! (F.continuous_phaseTrajectory D).comp
      (show Continuous (fun τ : Icc (-T) T => (τ.val,φ)) from
        continuous_subtype_val.prodMk continuous_const)

/-- Coordinate paths depend continuously on the source in the uniform norm. -/
theorem continuous_phaseTrajectoryOn (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (T : ℝ) :
    Continuous (F.phaseTrajectoryOn D T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  simpa only [Function.comp_def,Function.uncurry,phaseTrajectoryOn,ContinuousMap.coe_mk] using!
    (F.continuous_phaseTrajectory D).comp
      (show Continuous (fun x : realTypeSourceSubmodule p × Icc (-T) T => (x.2.val,x.1)) from
        (continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)

/-- Initial sources admissible throughout the given compact time interval. -/
def trajectoryDomain (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (T : ℝ) : Set (realTypeSourceSubmodule p) :=
  {φ | ∀ τ : Icc (-T) T, (τ.val,φ) ∈ F.imageDomain D}

/-- The compact-time source trajectory, with a harmless fallback off its asserted domain. -/
def imageTrajectoryOn (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (T : ℝ)
    (φ : realTypeSourceSubmodule p) : C(Icc (-T) T,realTypeSourceSubmodule p) :=
  ContinuousMap.mkD (fun τ => F.imageFlow D φ τ.val) 0

/-- Admissibility throughout a compact time interval is open in the initial source. -/
theorem isOpen_trajectoryDomain (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (T : ℝ) :
    IsOpen (F.trajectoryDomain D T) := by
  let G : realTypeSourceSubmodule p → C(Icc (-T) T,RealCoeff p × RealCoeff p) :=
    fun φ => (Birkhoff.decodeReal.compLeftContinuous ℝ (Icc (-T) T))
      (F.phaseTrajectoryOn D T φ)
  have hG : Continuous G := (Birkhoff.decodeReal.compLeftContinuous ℝ (Icc (-T) T)).continuous.comp
    (F.continuous_phaseTrajectoryOn D T)
  have he : F.trajectoryDomain D T =
      G ⁻¹' {g | range g ⊆ range (sourceRealBirkhoffMap hp hp1 t)} := by
    ext φ
    exact ⟨fun h _ ⟨τ,hτ⟩ => hτ ▸ h τ,fun h τ => h ⟨τ,rfl⟩⟩
  rw [he]
  exact (ContinuousMap.isOpen_setOfPred_range_subset D.real_image_open).preimage hG

/-- The path is continuous in time whenever all its times are admissible. -/
theorem continuous_imagePath (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (T : ℝ) (φ : realTypeSourceSubmodule p) (hφ : φ ∈ F.trajectoryDomain D T) :
    Continuous (fun τ : Icc (-T) T => F.imageFlow D φ τ.val) := by
  exact (F.continuousOn_imageFlow D).comp_continuous
    (f := fun τ : Icc (-T) T => (τ.val,φ))
    (continuous_subtype_val.prodMk continuous_const) hφ

/-- Evaluation gives the actual source flow at every admissible time. -/
theorem imageTrajectoryOn_apply (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (T : ℝ) (φ : realTypeSourceSubmodule p) (hφ : φ ∈ F.trajectoryDomain D T)
    (τ : Icc (-T) T) :
    F.imageTrajectoryOn D T φ τ = F.imageFlow D φ τ.val :=
  ContinuousMap.mkD_apply_of_continuous (F.continuous_imagePath D T φ hφ)

/-- Continuity in the uniform source trajectory norm on the open initial-data domain. -/
theorem continuousOn_imageTrajectoryOn (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (T : ℝ) :
    ContinuousOn (F.imageTrajectoryOn D T) (F.trajectoryDomain D T) := by
  apply ContinuousMap.continuousOn_mkD_of_uncurry
  exact (F.continuousOn_imageFlow D).comp
    (f := fun x : realTypeSourceSubmodule p × Icc (-T) T => (x.2.val,x.1))
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst).continuousOn
    (fun x hx => hx.1 x.2)


end NLS.ZakharovShabat.SourceActionFrequency
