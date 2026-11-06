import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Continuous evolution through a fixed homeomorphism

Joint continuity yields continuous dependence of complete trajectories
in the compact-open topology, and hence uniform convergence on each
compact time set in a uniform target space.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.Dynamics
variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

def conjugatedEvolution (e : E ≃ₜ F) (T : ℝ → F → F) (t : ℝ) (a : E) : E :=
  e.symm (T t (e a))

theorem conjugatedEvolution_coordinates (e : E ≃ₜ F) (T : ℝ → F → F) (t : ℝ) (a : E) :
    e (conjugatedEvolution e T t a)=T t (e a) := e.apply_symm_apply _

theorem conjugatedEvolution_zero (e : E ≃ₜ F) (T : ℝ → F → F)
    (hzero : ∀ b, T 0 b=b) (a : E) : conjugatedEvolution e T 0 a=a := by
  rw [conjugatedEvolution,hzero,e.symm_apply_apply]

theorem conjugatedEvolution_add (e : E ≃ₜ F) (T : ℝ → F → F)
    (hadd : ∀ t u b, T t (T u b)=T (t+u) b) (t u : ℝ) (a : E) :
    conjugatedEvolution e T t (conjugatedEvolution e T u a)=conjugatedEvolution e T (t+u) a := by
  simp only [conjugatedEvolution,e.apply_symm_apply,hadd]

theorem continuous_conjugatedEvolution (e : E ≃ₜ F) (T : ℝ → F → F)
    (hT : Continuous (fun x : ℝ × F => T x.1 x.2)) :
    Continuous (fun x : ℝ × E => conjugatedEvolution e T x.1 x.2) :=
  e.symm.continuous.comp (hT.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))

def conjugatedTrajectoryMap (e : E ≃ₜ F) (T : ℝ → F → F)
    (hT : Continuous (fun x : ℝ × F => T x.1 x.2)) : C(E,C(ℝ,E)) :=
  ContinuousMap.curry ⟨(fun x : E × ℝ => conjugatedEvolution e T x.2 x.1),
    (continuous_conjugatedEvolution e T hT).comp continuous_swap⟩

@[simp] theorem conjugatedTrajectoryMap_apply (e : E ≃ₜ F) (T : ℝ → F → F)
    (hT : Continuous (fun x : ℝ × F => T x.1 x.2)) (a : E) (t : ℝ) :
    conjugatedTrajectoryMap e T hT a t=conjugatedEvolution e T t a := rfl

theorem tendsto_conjugatedTrajectoryMap {ι : Type*} {l : Filter ι} {a : E} {u : ι → E}
    (e : E ≃ₜ F) (T : ℝ → F → F) (hT : Continuous (fun x : ℝ × F => T x.1 x.2))
    (hu : Tendsto u l (𝓝 a)) :
    Tendsto (fun i => conjugatedTrajectoryMap e T hT (u i)) l
      (𝓝 (conjugatedTrajectoryMap e T hT a)) :=
  (conjugatedTrajectoryMap e T hT).continuous.continuousAt.tendsto.comp hu

end NLS.Dynamics

namespace NLS.Dynamics
variable {E F : Type*} [UniformSpace E] [TopologicalSpace F]

theorem tendstoUniformlyOn_conjugatedEvolution {ι : Type*} {l : Filter ι} {a : E} {u : ι → E}
    (e : E ≃ₜ F) (T : ℝ → F → F) (hT : Continuous (fun x : ℝ × F => T x.1 x.2))
    (hu : Tendsto u l (𝓝 a)) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun i t => conjugatedEvolution e T t (u i))
      (fun t => conjugatedEvolution e T t a) l K :=
  (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
    (tendsto_conjugatedTrajectoryMap e T hT hu)) K hK

end NLS.Dynamics
