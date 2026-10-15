import NLS.ZakharovShabat.SourceBirkhoffOriginalAngleFlow

/-!
# An actual-source witness for the sign in equation (3.9)

The global Hilbert inverse realizes x₀=1 and y₀=0 by an actual source.
Its true angle-Hamiltonian velocity in x₀ is minus one, whereas the
printed expression evaluates to plus one.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection16OriginalData
variable {W₀ W V : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Every original package supplies an actual real source witnessing the wrong x sign. -/
theorem equation3_9_printed_sign_counterexample
    (D : SourceSection16OriginalData (p := 2) (by simp) (by norm_num) W₀ W V s) :
    ∃ φ : realTypeSourceSubmodule 2,
      (D.complex.hilbertRealHomeomorph φ).1 0 = 1 ∧
      (D.complex.hilbertRealHomeomorph φ).2 0 = 0 ∧
      (sourceBirkhoffJacobian (by simp) (by norm_num) s φ.val
        (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) 0 s φ.val)).1 0 = -1 ∧
      (D.complex.hilbertRealHomeomorph φ).1 0 /
        (((D.complex.hilbertRealHomeomorph φ).1 0)^2+
          ((D.complex.hilbertRealHomeomorph φ).2 0)^2) = 1 := by
  let z : RealCoeff 2 × RealCoeff 2 := (lp.single 2 0 1,0)
  let φ := D.complex.hilbertRealHomeomorph.symm z
  have hout : D.complex.hilbertRealHomeomorph φ = z :=
    D.complex.hilbertRealHomeomorph.apply_symm_apply z
  have hact : (sourceRealAction (by simp) (by norm_num) φ.val φ.property 0).re = 1/2 := by
    rw [← D.complex.hilbert_pairAction_eq,hout]
    norm_num [RealCoeff.pairAction,z]
  have hgap : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) 0 ≠ 0 := by
    intro hg
    have hz := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero
      (by simp) (by norm_num) φ.val φ.property 0).2.2.mpr
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hg)
    rw [hz,Complex.zero_re] at hact
    norm_num at hact
  refine ⟨φ,?_,?_,?_,?_⟩
  · rw [hout]; norm_num [z]
  · rw [hout]; rfl
  · rw [equation3_9 D 0 φ hgap,hout]
    change ((RealCoeff.actionReductionVector z 0).1 0 : ℂ) = -1
    norm_num [RealCoeff.actionReductionVector,RealCoeff.pairAction,RealCoeff.pairMode,z]
  · rw [hout]; norm_num [z]



end NLS.ZakharovShabat.SourceSection16OriginalData
