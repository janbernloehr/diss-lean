import NLS.ZakharovShabat.PhysicalSpectralPoisson
import NLS.ZakharovShabat.PhysicalHamiltonianDirection

/-! # Physical action Hamiltonian fields

The actual physical action field rotates one Birkhoff coordinate pair
and is tangent to the original real Hilbert space. At a collapsed gap
its full cotangent and vector field vanish. A constructed complex
extension of the intrinsic physical map has these exact velocities,
without a supplied normalized family or Hamiltonian-field premise.
-/

noncomputable section
open Set Metric MeasureTheory Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

namespace SourceSection14OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (D : SourceSection14OriginalData (by simp) (by norm_num) W₀ W V s)
include D

/-- The actual physical action field rotates precisely one Birkhoff coordinate pair. -/
theorem physicalBirkhoffMap_actionHamiltonian (k n : ℤ) (u : physicalRealSubmodule) :
    (fderiv ℂ (fun v => (physicalBirkhoffMap s v).fst n) u.val)
      (physicalHamiltonianVector (physicalIndexedAction k) u.val) =
        -(physicalBirkhoffMap s u.val).snd k*(if n = k then 1 else 0) ∧
    (fderiv ℂ (fun v => (physicalBirkhoffMap s v).snd n) u.val)
      (physicalHamiltonianVector (physicalIndexedAction k) u.val) =
        (physicalBirkhoffMap s u.val).fst k*(if n = k then 1 else 0) := by
  rw [fderiv_apply_physicalHamiltonianVector,fderiv_apply_physicalHamiltonianVector]
  exact D.physicalBirkhoffMap_action_brackets k n u

/-- Closed physical gaps have zero complex Birkhoff coordinate pairs on the real form. -/
theorem physicalBirkhoffMap_coordinates_zero_of_collapsed (n : ℤ) (u : physicalRealSubmodule)
    (hg : physicalPeriodicLeft u.val n = physicalPeriodicRight u.val n) :
    (physicalBirkhoffMap s u.val).fst n = 0 ∧ (physicalBirkhoffMap s u.val).snd n = 0 := by
  have hgap : sourcePeriodicGapDisplacement (by simp) (by norm_num)
      (sourcePhysicalL2Equiv.symm u.val) n = 0 := by
    by_contra hne
    exact ((physicalPeriodicGap_ne_iff u.val n).mpr hne) hg
  have hi : physicalIndexedAction n u.val = 0 :=
    (sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
      n (sourcePhysicalL2Equiv.symm u.val) u.property).2.2.mpr hgap
  have h := D.physicalRealActionAngleHomeomorph_intrinsic_formula u n
  simp only [hi,Complex.zero_re,mul_zero,Real.sqrt_zero,zero_mul] at h
  rw [← D.physicalBirkhoffMap_real u]
  change ((D.physicalRealActionAngleHomeomorph u).fst n : ℂ) = 0 ∧
    ((D.physicalRealActionAngleHomeomorph u).snd n : ℂ) = 0
  simp only [h.1,h.2,Complex.ofReal_zero,and_self]

/-- The entire physical action cotangent vanishes at a collapsed real gap. -/
theorem physicalIndexedAction_fderiv_zero_of_collapsed (n : ℤ) (u : physicalRealSubmodule)
    (hg : physicalPeriodicLeft u.val n = physicalPeriodicRight u.val n) :
    fderiv ℂ (physicalIndexedAction n) u.val = 0 := by
  have h := D.physicalBirkhoffMap_coordinates_zero_of_collapsed n u hg
  rw [D.physicalIndexedAction_fderiv u.val (D.physicalBirkhoffDomain_real u) n,h.1,h.2]
  ext h
  simp

end SourceSection14OriginalData

/-- Every physical action Hamiltonian is tangent to the physical real Hilbert space. -/
theorem physicalHamiltonianVector_indexedAction_real (n : ℤ) (u : physicalRealSubmodule) :
    physicalHamiltonianVector (physicalIndexedAction n) u.val ∈ physicalRealSubmodule := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  exact physicalHamiltonianVector_mem_real _ u
    ((A.physicalIndexedAction_analytic n u.val (A.physicalBirkhoffDomain_real u)).differentiableAt)
    (fun v => (physicalIndexedAction_nonneg v n).2)

/-- A collapsed action has zero physical Hamiltonian field, not only zero coordinate velocities. -/
theorem physicalHamiltonianVector_indexedAction_zero_of_collapsed (n : ℤ) (u : physicalRealSubmodule)
    (hg : physicalPeriodicLeft u.val n = physicalPeriodicRight u.val n) :
    physicalHamiltonianVector (physicalIndexedAction n) u.val = 0 := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  rw [physicalHamiltonianVector,
    D.toSourceSection14OriginalData.physicalIndexedAction_fderiv_zero_of_collapsed n u hg,
    physicalHamiltonianDirection_zero]

/-- A constructed complex extension gives the physical action fields their exact coordinate velocities. -/
theorem intrinsicPhysicalBirkhoffMap_actionHamiltonian_extension :
    ∃ U : Set IntervalPairL2, ∃ F : IntervalPairL2 → CoeffPair 2,
      IsOpen U ∧ (∀ u : physicalRealSubmodule, u.val ∈ U) ∧ AnalyticOnNhd ℂ F U ∧
      (∀ u : physicalRealSubmodule, physicalRealTargetComplex (intrinsicPhysicalBirkhoffMap u) = F u.val) ∧
      ∀ (u : physicalRealSubmodule) (k n : ℤ),
        (fderiv ℂ (fun v => (F v).fst n) u.val) (physicalHamiltonianVector (physicalIndexedAction k) u.val) =
          -(F u.val).snd k*(if n = k then 1 else 0) ∧
        (fderiv ℂ (fun v => (F v).snd n) u.val) (physicalHamiltonianVector (physicalIndexedAction k) u.val) =
          (F u.val).fst k*(if n = k then 1 else 0) := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  exact ⟨physicalBirkhoffDomain V,physicalBirkhoffMap s,A.physicalBirkhoffDomain_open,
    A.physicalBirkhoffDomain_real,A.physicalBirkhoffMap_analytic,A.intrinsicPhysicalBirkhoffMap_complex,
    fun u k n => A.physicalBirkhoffMap_actionHamiltonian k n u⟩

end NLS.ZakharovShabat
