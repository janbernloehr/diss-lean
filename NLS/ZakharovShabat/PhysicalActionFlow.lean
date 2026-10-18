import NLS.ZakharovShabat.PhysicalHamiltonianAnalytic
import NLS.ZakharovShabat.PhysicalActionHamiltonian
import NLS.ZakharovShabat.SourceHilbertActionRotation
import NLS.ZakharovShabat.SourceAngularOriginalCanonicalDifferentials

/-! # Complete physical action trajectories

The intrinsic physical Birkhoff homeomorphism transports one-coordinate
rotations to the original real L2 space for every real time. Their derivatives
are the literal physical action Hamiltonian fields, with the positive-sine
orientation (-y,x). The construction agrees with every original source
realization and preserves the entire monodromy discriminant.
-/

noncomputable section
open Set Metric MeasureTheory Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

namespace SourceSection14OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (D : SourceSection14OriginalData (by simp) (by norm_num) W₀ W V s)
include D

/-- The physical action field is the realization of the original spectral action field. -/
theorem physicalHamiltonianVector_indexedAction_eq_source (n : ℤ) (u : physicalRealSubmodule) :
    physicalHamiltonianVector (physicalIndexedAction n) u.val =
      sourcePhysicalL2 (sourceHamiltonianVector le_rfl
        (sourceComplexAction (by simp) (by norm_num) n) (sourcePhysicalL2Equiv.symm u.val)) := by
  rw [physicalHamiltonianVector_eq_source _ _
    (D.physicalIndexedAction_analytic n _ (D.physicalBirkhoffDomain_real u)).differentiableAt]
  have he : physicalIndexedAction n ∘ sourcePhysicalL2 = sourceIndexedAction (by simp) (by norm_num) n := by
    funext φ
    simp only [Function.comp_apply,physicalIndexedAction,← sourcePhysicalL2Equiv_apply,
      LinearIsometryEquiv.symm_apply_apply]
  have hreal : IsRealType (CoeffPair.toMax 2 (sourcePhysicalL2Equiv.symm u.val)) := u.property
  have hc := D.previous.action_original_fderiv_eq_complexAction (sourcePhysicalL2Equiv.symm u.val)
    (D.complex.source_subset (D.complex.real_subset hreal)) hreal n
  rw [he,sourceHamiltonianVector,hc]
  rfl

/-- Exact source coordinates of the independently defined physical map. -/
theorem intrinsicPhysicalBirkhoffMap_source (φ : realTypeSourceSubmodule 2) :
    (intrinsicPhysicalBirkhoffMap (realSourcePhysicalL2Equiv φ)).ofLp =
      D.complex.hilbertRealHomeomorph φ := by
  rw [D.intrinsicPhysicalBirkhoffMap_eq,D.physicalRealActionAngleHomeomorph_apply,
    LinearIsometryEquiv.symm_apply_apply,D.realActionAngleMap_eq]
  rfl

end SourceSection14OriginalData

/-- Rotate one real physical action coordinate for any real time. -/
def physicalActionFlow (u : physicalRealSubmodule) (k : ℤ) (t : ℝ) : physicalRealSubmodule :=
  intrinsicPhysicalBirkhoffHomeomorph.symm
    (WithLp.toLp 2 (RealCoeff.actionRotation (intrinsicPhysicalBirkhoffMap u).ofLp k t))

/-- The actual physical flow has the prescribed complete coordinate rotation. -/
@[simp] theorem intrinsicPhysicalBirkhoffMap_actionFlow (u : physicalRealSubmodule) (k : ℤ) (t : ℝ) :
    intrinsicPhysicalBirkhoffMap (physicalActionFlow u k t) =
      WithLp.toLp 2 (RealCoeff.actionRotation (intrinsicPhysicalBirkhoffMap u).ofLp k t) :=
  intrinsicPhysicalBirkhoffHomeomorph_right_inv _

@[simp] theorem physicalActionFlow_zero (u : physicalRealSubmodule) (k : ℤ) :
    physicalActionFlow u k 0 = u := by
  simp only [physicalActionFlow,RealCoeff.actionRotation_zero,WithLp.toLp_ofLp,
    intrinsicPhysicalBirkhoffHomeomorph_left_inv]

/-- The physical flow is a group in time. -/
theorem physicalActionFlow_add (u : physicalRealSubmodule) (k : ℤ) (t r : ℝ) :
    physicalActionFlow (physicalActionFlow u k t) k r = physicalActionFlow u k (t+r) := by
  apply intrinsicPhysicalBirkhoffHomeomorph.injective
  simp only [intrinsicPhysicalBirkhoffHomeomorph_apply,intrinsicPhysicalBirkhoffMap_actionFlow,
    WithLp.ofLp_toLp,RealCoeff.actionRotation_add]

/-- Every step is reversed by negative time. -/
@[simp] theorem physicalActionFlow_neg (u : physicalRealSubmodule) (k : ℤ) (t : ℝ) :
    physicalActionFlow (physicalActionFlow u k t) k (-t) = u := by
  rw [physicalActionFlow_add,add_neg_cancel,physicalActionFlow_zero]

namespace SourceSection14OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (D : SourceSection14OriginalData (by simp) (by norm_num) W₀ W V s)
include D

/-- The intrinsic physical rotation agrees with every original source construction. -/
theorem physicalActionFlow_eq_source (u : physicalRealSubmodule) (k : ℤ) (t : ℝ) :
    physicalActionFlow u k t = realSourcePhysicalL2Equiv
      (D.complex.hilbertActionRotation (realSourcePhysicalL2Equiv.symm u) k t) := by
  apply intrinsicPhysicalBirkhoffHomeomorph.injective
  simp only [intrinsicPhysicalBirkhoffHomeomorph_apply]
  apply WithLp.ofLp_injective
  rw [intrinsicPhysicalBirkhoffMap_actionFlow,WithLp.ofLp_toLp,
    D.intrinsicPhysicalBirkhoffMap_source,D.complex.hilbertRealHomeomorph_actionRotation]
  congr 1
  have h := D.intrinsicPhysicalBirkhoffMap_source (realSourcePhysicalL2Equiv.symm u)
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

/-- At every time the physical curve solves the literal L2 action Hamiltonian equation. -/
theorem hasDerivAt_physicalActionFlow (u : physicalRealSubmodule) (k : ℤ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (physicalActionFlow u k t).val)
      (physicalHamiltonianVector (physicalIndexedAction k) (physicalActionFlow u k t).val) t := by
  have hd := (sourcePhysicalL2.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (D.complex.hasDerivAt_hilbertActionRotation_actionHamiltonian (realSourcePhysicalL2Equiv.symm u) k t)
  have he (r : ℝ) : (physicalActionFlow u k r).val = sourcePhysicalL2
      (D.complex.hilbertActionRotation (realSourcePhysicalL2Equiv.symm u) k r).val := by
    rw [D.physicalActionFlow_eq_source]
    exact sourcePhysicalL2Equiv_apply _
  have hv := D.physicalHamiltonianVector_indexedAction_eq_source k (physicalActionFlow u k t)
  have hinv : sourcePhysicalL2Equiv.symm (physicalActionFlow u k t).val =
      (D.complex.hilbertActionRotation (realSourcePhysicalL2Equiv.symm u) k t).val := by
    rw [he t,← sourcePhysicalL2Equiv_apply,LinearIsometryEquiv.symm_apply_apply]
  rw [hinv] at hv
  rw [hv]
  convert! hd using 1
  funext r
  exact he r

/-- The whole physical monodromy discriminant is preserved for all times. -/
theorem l2Discriminant_physicalActionFlow (u : physicalRealSubmodule) (k : ℤ) (t : ℝ) :
    l2Discriminant (physicalActionFlow u k t).val = l2Discriminant u.val := by
  have h := D.complex.discriminant_hilbertActionRotation (realSourcePhysicalL2Equiv.symm u) k t
  funext z
  have he := congrFun h z
  rw [canonicalDiscriminant_eq_l2_source,canonicalDiscriminant_eq_l2_source] at he
  change l2Discriminant (sourcePhysicalL2 _) z =
    l2Discriminant (sourcePhysicalL2 (sourcePhysicalL2Equiv.symm u.val)) z at he
  rw [sourcePhysicalL2_equiv_symm] at he
  rw [D.physicalActionFlow_eq_source]
  change l2Discriminant (sourcePhysicalL2Equiv _) z = _
  simpa only [sourcePhysicalL2Equiv_apply] using he

end SourceSection14OriginalData

end NLS.ZakharovShabat
