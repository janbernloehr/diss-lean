import NLS.ZakharovShabat.PhysicalActionFlowProperties
import NLS.SequenceSpaces.RealActionRotationProperties

/-! # Continuous groups of physical action flows

The selected pair has the exact sine-cosine rotation and every other pair is
fixed. All action flows commute, have period two pi, and depend jointly
continuously on time and the original physical initial state. Every fixed
time gives a homeomorphism with inverse at negative time. The period claim
does not assert a least period for stationary trajectories.
-/

noncomputable section
open Set Metric MeasureTheory Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- The selected physical pair follows the exact sine and cosine rotation. -/
theorem physicalActionFlow_coordinates_same (u : physicalRealSubmodule) (k : ℤ) (t : ℝ) :
    (intrinsicPhysicalBirkhoffMap (physicalActionFlow u k t)).fst k =
      Real.cos t*(intrinsicPhysicalBirkhoffMap u).fst k-Real.sin t*(intrinsicPhysicalBirkhoffMap u).snd k ∧
    (intrinsicPhysicalBirkhoffMap (physicalActionFlow u k t)).snd k =
      Real.sin t*(intrinsicPhysicalBirkhoffMap u).fst k+Real.cos t*(intrinsicPhysicalBirkhoffMap u).snd k := by
  rw [intrinsicPhysicalBirkhoffMap_actionFlow]
  exact RealCoeff.actionRotation_apply_same _ k t

/-- Every other physical coordinate pair remains fixed. -/
theorem physicalActionFlow_coordinates_ne (u : physicalRealSubmodule) (k n : ℤ) (hn : n ≠ k) (t : ℝ) :
    (intrinsicPhysicalBirkhoffMap (physicalActionFlow u k t)).fst n = (intrinsicPhysicalBirkhoffMap u).fst n ∧
    (intrinsicPhysicalBirkhoffMap (physicalActionFlow u k t)).snd n = (intrinsicPhysicalBirkhoffMap u).snd n := by
  rw [intrinsicPhysicalBirkhoffMap_actionFlow]
  exact RealCoeff.actionRotation_apply_ne _ k n hn t

/-- All physical action trajectories have period two pi, including stationary ones. -/
theorem physicalActionFlow_periodic (u : physicalRealSubmodule) (k : ℤ) :
    Function.Periodic (physicalActionFlow u k) (2*Real.pi) := by
  intro t
  apply intrinsicPhysicalBirkhoffHomeomorph.injective
  simp only [intrinsicPhysicalBirkhoffHomeomorph_apply,intrinsicPhysicalBirkhoffMap_actionFlow,
    RealCoeff.actionRotation,Real.cos_add_two_pi,Real.sin_add_two_pi]

/-- Complete physical action flows commute for arbitrary indices and times. -/
theorem physicalActionFlow_comm (u : physicalRealSubmodule) (k l : ℤ) (t r : ℝ) :
    physicalActionFlow (physicalActionFlow u k t) l r = physicalActionFlow (physicalActionFlow u l r) k t := by
  apply intrinsicPhysicalBirkhoffHomeomorph.injective
  simp only [intrinsicPhysicalBirkhoffHomeomorph_apply,intrinsicPhysicalBirkhoffMap_actionFlow,
    WithLp.ofLp_toLp,RealCoeff.actionRotation_comm]

/-- The physical action flow is jointly continuous in time and the original L2 initial state. -/
theorem continuous_physicalActionFlow (k : ℤ) :
    Continuous (fun x : ℝ × physicalRealSubmodule => physicalActionFlow x.2 k x.1) := by
  have hm : Continuous intrinsicPhysicalBirkhoffMap := continuous_iff_continuousAt.mpr
    (fun u => (intrinsicPhysicalBirkhoffMap_analytic u (mem_univ u)).continuousAt)
  have hp : Continuous (fun x : ℝ × physicalRealSubmodule =>
      (x.1,physicalRealTargetEquiv (intrinsicPhysicalBirkhoffMap x.2))) :=
    continuous_fst.prodMk (physicalRealTargetEquiv.continuous.comp (hm.comp continuous_snd))
  have hc := intrinsicPhysicalBirkhoffHomeomorph.symm.continuous.comp
    (physicalRealTargetEquiv.symm.continuous.comp ((RealCoeff.continuous_actionRotation k).comp hp))
  exact hc

/-- Each fixed-time action map is continuous in the initial physical state. -/
theorem continuous_physicalActionFlow_time (k : ℤ) (t : ℝ) :
    Continuous (fun u : physicalRealSubmodule => physicalActionFlow u k t) := by
  have h := (continuous_physicalActionFlow k).comp
    (show Continuous (fun u : physicalRealSubmodule => (t,u)) from continuous_const.prodMk continuous_id)
  convert! h using 1

/-- Every action-flow time is a physical homeomorphism, with inverse at negative time. -/
def physicalActionFlowHomeomorph (k : ℤ) (t : ℝ) : physicalRealSubmodule ≃ₜ physicalRealSubmodule where
  toFun u := physicalActionFlow u k t
  invFun u := physicalActionFlow u k (-t)
  left_inv u := physicalActionFlow_neg u k t
  right_inv u := by simpa only [neg_neg] using physicalActionFlow_neg u k (-t)
  continuous_toFun := continuous_physicalActionFlow_time k t
  continuous_invFun := continuous_physicalActionFlow_time k (-t)

end NLS.ZakharovShabat
