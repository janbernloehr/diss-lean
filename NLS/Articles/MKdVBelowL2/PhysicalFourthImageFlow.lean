import NLS.Articles.MKdVBelowL2.FourthHamiltonianPhaseFamily
import NLS.ZakharovShabat.SourceActionPhaseTrajectories

/-! # Local and small-data H₄ rotations on original physical distribution pairs

The frequency is the verified cubic-plus-normalized H₄ family. The actual
inverse of the fixed Theorem 1.2 Birkhoff map supplies the physical source
curve on its open image domain. Continuity is in the full uniform trajectory
norm. Restriction to the real mKdV diagonal and agreement with smooth PDE
solutions remain separate requirements of Theorem 1.1.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual admissible time-input pairs for the fixed physical H₄ rotation. -/
def fourthPhysicalImageDomain (hp : p ≠ ⊤) (hp1 : 1 < p) : Set (ℝ × PhysicalRealInput p) :=
  {x | (x.1,physicalRealCoefficientsCL x.2) ∈ (fourthSourcePhaseFrequency hp hp1).imageDomain
    (originalBirkhoffChart hp hp1).data.complex}

/-- Lift the actual Hamiltonian phases back to the original period-one distributions. -/
def fourthPhysicalImageFlow (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalRealInput p) (τ : ℝ) :
    PhysicalRealInput p :=
  physicalRealCoefficientsCL.symm ((fourthSourcePhaseFrequency hp hp1).imageFlow
    (originalBirkhoffChart hp hp1).data.complex (physicalRealCoefficientsCL u) τ)

/-- Time zero is admissible for every original physical input. -/
theorem zero_mem_fourthPhysicalImageDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalRealInput p) :
    (0,u) ∈ fourthPhysicalImageDomain hp hp1 :=
  (fourthSourcePhaseFrequency hp hp1).zero_mem_imageDomain _ _

@[simp] theorem fourthPhysicalImageFlow_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalRealInput p) :
    fourthPhysicalImageFlow hp hp1 u 0 = u := by
  unfold fourthPhysicalImageFlow
  rw [SourceActionFrequency.imageFlow_zero,ContinuousLinearEquiv.symm_apply_apply]

/-- The physical time-source domain is open in the actual distribution norm. -/
theorem isOpen_fourthPhysicalImageDomain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsOpen (fourthPhysicalImageDomain hp hp1) :=
  ((fourthSourcePhaseFrequency hp hp1).isOpen_imageDomain _).preimage
    (continuous_fst.prodMk (physicalRealCoefficientsCL.continuous.comp continuous_snd))

/-- Source inversion is jointly continuous on exactly its asserted domain. -/
theorem continuousOn_fourthPhysicalImageFlow (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ContinuousOn (fun x : ℝ × PhysicalRealInput p => fourthPhysicalImageFlow hp hp1 x.2 x.1)
      (fourthPhysicalImageDomain hp hp1) := by
  let F := fourthSourcePhaseFrequency hp hp1
  let D := (originalBirkhoffChart hp hp1).data.complex
  let e := physicalRealCoefficientsCL (p := p)
  have hL : Continuous (fun x : ℝ × PhysicalRealInput p => (x.1,e x.2)) :=
    continuous_fst.prodMk (e.continuous.comp continuous_snd)
  have hi : ContinuousOn (fun x : ℝ × PhysicalRealInput p => F.imageFlow D (e x.2) x.1)
      (fourthPhysicalImageDomain hp hp1) :=
    (F.continuousOn_imageFlow D).comp (f := fun x : ℝ × PhysicalRealInput p => (x.1,e x.2)) hL.continuousOn (fun _ h => h)
  exact e.symm.continuous.comp_continuousOn hi

/-- Admissible original physical inputs for a complete compact time interval. -/
def fourthPhysicalTrajectoryDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ) : Set (PhysicalRealInput p) :=
  physicalRealCoefficientsCL ⁻¹' (fourthSourcePhaseFrequency hp hp1).trajectoryDomain
    (originalBirkhoffChart hp hp1).data.complex T

/-- The whole physical source path, retaining the original uniform trajectory norm. -/
def fourthPhysicalTrajectoryOn (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ) (u : PhysicalRealInput p) :
    C(Icc (-T) T,PhysicalRealInput p) :=
  (physicalRealCoefficientsCL.symm.toContinuousLinearMap.compLeftContinuous ℝ (Icc (-T) T))
    ((fourthSourcePhaseFrequency hp hp1).imageTrajectoryOn
      (originalBirkhoffChart hp hp1).data.complex T (physicalRealCoefficientsCL u))

/-- The common compact-time existence domain is open in the initial data. -/
theorem isOpen_fourthPhysicalTrajectoryDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ) :
    IsOpen (fourthPhysicalTrajectoryDomain hp hp1 T) :=
  ((fourthSourcePhaseFrequency hp hp1).isOpen_trajectoryDomain _ T).preimage physicalRealCoefficientsCL.continuous

/-- Every path value is the actual inverse lift at its original physical time. -/
theorem fourthPhysicalTrajectoryOn_apply (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ)
    (u : PhysicalRealInput p) (hu : u ∈ fourthPhysicalTrajectoryDomain hp hp1 T) (τ : Icc (-T) T) :
    fourthPhysicalTrajectoryOn hp hp1 T u τ = fourthPhysicalImageFlow hp hp1 u τ.val := by
  change physicalRealCoefficientsCL.symm ((fourthSourcePhaseFrequency hp hp1).imageTrajectoryOn
    (originalBirkhoffChart hp hp1).data.complex T (physicalRealCoefficientsCL u) τ) = _
  rw [SourceActionFrequency.imageTrajectoryOn_apply _ _ T _ hu τ]
  rfl

/-- Continuous initial-data dependence holds in C([-T,T],FL_r^p), with the
uniform norm rather than merely pointwise convergence in time. -/
theorem continuousOn_fourthPhysicalTrajectoryOn (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ) :
    ContinuousOn (fourthPhysicalTrajectoryOn hp hp1 T) (fourthPhysicalTrajectoryDomain hp hp1 T) :=
  (physicalRealCoefficientsCL.symm.toContinuousLinearMap.compLeftContinuous ℝ (Icc (-T) T)).continuous.comp_continuousOn
    (((fourthSourcePhaseFrequency hp hp1).continuousOn_imageTrajectoryOn _ T).comp
      physicalRealCoefficientsCL.continuous.continuousOn (fun _ h => h))

/-- One positive time and one open neighborhood work for all nearby physical
inputs, and the complete source trajectories vary continuously there. -/
theorem exists_local_fourthPhysicalTrajectory (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalRealInput p) :
    ∃ T > 0, ∃ U : Set (PhysicalRealInput p), IsOpen U ∧ u ∈ U ∧
      U ⊆ fourthPhysicalTrajectoryDomain hp hp1 T ∧ ContinuousOn (fourthPhysicalTrajectoryOn hp hp1 T) U := by
  obtain ⟨T,hT,V,hV,hu,hmap⟩ := (fourthSourcePhaseFrequency hp hp1).exists_local_imageFlow
    (originalBirkhoffChart hp hp1).data.complex (physicalRealCoefficientsCL u)
  let U := physicalRealCoefficientsCL ⁻¹' V
  have hU : U ⊆ fourthPhysicalTrajectoryDomain hp hp1 T := by
    intro v hv τ
    exact hmap _ hv τ.val τ.property
  exact ⟨T,hT,U,hV.preimage physicalRealCoefficientsCL.continuous,hu,hU,
    (continuousOn_fourthPhysicalTrajectoryOn hp hp1 T).mono hU⟩

/-- One open physical neighborhood of zero is chosen before every time
interval. The rotation lift is global there and has continuous compact-time
trajectory maps; the same neighborhood is invariant under every time step. -/
theorem exists_global_small_fourthPhysicalTrajectory (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ U : Set (PhysicalRealInput p), IsOpen U ∧ (0 : PhysicalRealInput p) ∈ U ∧
      (∀ T : ℝ, U ⊆ fourthPhysicalTrajectoryDomain hp hp1 T ∧
        ContinuousOn (fourthPhysicalTrajectoryOn hp hp1 T) U) ∧
      ∀ u ∈ U, ∀ τ : ℝ, fourthPhysicalImageFlow hp hp1 u τ ∈ U := by
  obtain ⟨V,hV,hzero,_,hmap,hinv⟩ := (fourthSourcePhaseFrequency hp hp1).exists_invariant_small_phaseFlow
    (originalBirkhoffChart hp hp1).data.complex
  let U := physicalRealCoefficientsCL ⁻¹' V
  have hU (T : ℝ) : U ⊆ fourthPhysicalTrajectoryDomain hp hp1 T := by
    intro u hu τ
    exact hmap _ hu τ.val
  refine ⟨U,hV.preimage physicalRealCoefficientsCL.continuous,?_,
    fun T => ⟨hU T,(continuousOn_fourthPhysicalTrajectoryOn hp hp1 T).mono (hU T)⟩,?_⟩
  · change physicalRealCoefficientsCL (0 : PhysicalRealInput p) ∈ V
    simpa only [map_zero] using hzero
  · intro u hu τ
    change physicalRealCoefficientsCL (physicalRealCoefficientsCL.symm _) ∈ V
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hinv _ hu τ

end NLS.Articles.MKdVBelowL2
