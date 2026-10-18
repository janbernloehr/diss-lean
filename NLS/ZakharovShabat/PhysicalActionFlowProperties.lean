import NLS.ZakharovShabat.PhysicalActionFlow
import NLS.FunctionalAnalysis.AutonomousODEUniqueness

/-! # Uniqueness and conservation for physical action flows

The constructed trajectory solves the actual physical Hamiltonian equation
for all real times. Uniqueness holds against any competing complex L2 curve
with the same real initial value. Every action, the physical Hilbert norm,
and the entire discriminant are conserved. A collapsed selected gap gives
a stationary trajectory.
-/

noncomputable section
open Set Metric MeasureTheory Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- Every real physical input has a global trajectory of its actual action Hamiltonian. -/
theorem hasDerivAt_physicalActionFlow (u : physicalRealSubmodule) (k : ℤ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (physicalActionFlow u k t).val)
      (physicalHamiltonianVector (physicalIndexedAction k) (physicalActionFlow u k t).val) t := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  exact D.toSourceSection14OriginalData.hasDerivAt_physicalActionFlow u k t

/-- Any solution in the physical complex L2 space with the same initial value is this trajectory. -/
theorem physicalActionFlow_unique (u : physicalRealSubmodule) (k : ℤ)
    (g : ℝ → IntervalPairL2) (hzero : g 0 = u.val)
    (hg : ∀ t, HasDerivAt g (physicalHamiltonianVector (physicalIndexedAction k) (g t)) t) :
    g = fun t => (physicalActionFlow u k t).val := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  have he : EqOn (fun t => (physicalActionFlow u k t).val) g univ := by
    apply NLS.FunctionalAnalysis.eqOn_of_autonomous_hasDerivAt isOpen_univ isPreconnected_univ
      (v := physicalHamiltonianVector (physicalIndexedAction k)) (t₀ := 0)
    · intro t _
      exact (((analyticOnNhd_physicalHamiltonianVector (A.physicalIndexedAction_analytic k))
        _ (A.physicalBirkhoffDomain_real (physicalActionFlow u k t))).restrictScalars (𝕜 := ℝ)).contDiffAt
    · intro t _
      exact hasDerivAt_physicalActionFlow u k t
    · intro t _
      exact hg t
    · exact mem_univ 0
    · simpa only [physicalActionFlow_zero] using hzero.symm
  exact funext (fun t => (he (mem_univ t)).symm)

/-- The whole physical monodromy discriminant remains constant for all real times. -/
theorem l2Discriminant_physicalActionFlow (u : physicalRealSubmodule) (k : ℤ) (t : ℝ) :
    l2Discriminant (physicalActionFlow u k t).val = l2Discriminant u.val := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  exact D.toSourceSection14OriginalData.l2Discriminant_physicalActionFlow u k t

/-- The intrinsic coordinates have precisely the original physical action radii. -/
theorem intrinsicPhysicalBirkhoffMap_pairAction (u : physicalRealSubmodule) (n : ℤ) :
    RealCoeff.pairAction (intrinsicPhysicalBirkhoffMap u).ofLp n = (physicalIndexedAction n u.val).re := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  have he := A.intrinsicPhysicalBirkhoffMap_source (realSourcePhysicalL2Equiv.symm u)
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  rw [he,A.complex.hilbert_pairAction_eq]
  exact (congrArg Complex.re (sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num)
    n (sourcePhysicalL2Equiv.symm u.val) u.property)).symm

/-- The complete physical trajectory preserves every action. -/
theorem physicalIndexedAction_actionFlow (u : physicalRealSubmodule) (k n : ℤ) (t : ℝ) :
    physicalIndexedAction n (physicalActionFlow u k t).val = physicalIndexedAction n u.val := by
  apply Complex.ext
  · rw [← intrinsicPhysicalBirkhoffMap_pairAction,← intrinsicPhysicalBirkhoffMap_pairAction,
      intrinsicPhysicalBirkhoffMap_actionFlow,WithLp.ofLp_toLp,RealCoeff.pairAction_actionRotation]
  · exact (physicalIndexedAction_nonneg _ n).2.trans (physicalIndexedAction_nonneg u n).2.symm

/-- The original physical Hilbert norm is conserved at all times. -/
theorem physicalActionFlow_norm (u : physicalRealSubmodule) (k : ℤ) (t : ℝ) :
    ‖physicalActionFlow u k t‖ = ‖u‖ := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  have hs : ‖physicalActionFlow u k t‖^2/2 = ‖u‖^2/2 := by
    rw [← A.physical_sum_actions,← A.physical_sum_actions]
    apply tsum_congr
    intro n
    rw [physicalIndexedAction_actionFlow]
  nlinarith [norm_nonneg (physicalActionFlow u k t),norm_nonneg u]

/-- A closed selected gap gives a stationary trajectory for all times. -/
theorem physicalActionFlow_eq_self_of_collapsed (u : physicalRealSubmodule) (k : ℤ)
    (hg : physicalPeriodicLeft u.val k = physicalPeriodicRight u.val k) (t : ℝ) :
    physicalActionFlow u k t = u := by
  have he := physicalActionFlow_unique u k (fun _ => u.val) rfl (fun r => by
    rw [physicalHamiltonianVector_indexedAction_zero_of_collapsed k u hg]
    exact hasDerivAt_const r u.val)
  apply Subtype.ext
  exact (congrFun he t).symm

end NLS.ZakharovShabat
