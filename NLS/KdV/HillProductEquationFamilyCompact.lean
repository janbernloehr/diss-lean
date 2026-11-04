import NLS.KdV.HillProductEquationUniformDiagonalUpper
import NLS.KdV.HillProductEquationUniformDiagonalTail
import NLS.SequenceSpaces.PositiveDiagonalFamilyCompact

/-! At every actual real source, the entire family of original Hill
period Jacobians has compact closure in the FULL operator norm. This
does not by itself identify escaping-index limits or prove them invertible. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem sequenceJacobian_actual_real_family_totallyBounded (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    TotallyBounded (range (fun n : ℕ+ => P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q))) := by
  let J (n : ℕ+) := P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)
  let I := ContinuousLinearMap.id ℂ (lp (fun _ : ℕ+ => ℂ) 2)
  let R (n : ℕ+) := J n-I
  obtain ⟨M,hM,hdiag⟩ := P.exists_actual_real_uniform_diagonal_upper q hq hr
  obtain ⟨K,hK,hbound⟩ := P.exists_uniform_actual_real_off_diagonal_bound q hq hr
  let b : lp (fun _ : ℕ+ => ℂ) 2 := (K:ℂ) • hillHminusGapWidthDisplacement ⟨q,hr⟩
  let κ : ℕ+ → lp (fun _ : ℕ+ => ℂ) 2 := fun m => LpSequence.positiveRestriction (hillFreeInteractionKernel m)
  have hκ (m : ℕ+) : ‖κ m‖ ≤ hillFreeInteractionConstant :=
    (LpSequence.norm_positiveRestriction_le _).trans (norm_hillFreeInteractionKernel_le m)
  have hrdiag (n m : ℕ+) : R n (lp.single 2 m 1) m = J n (lp.single 2 m 1) m-1 := by
    simp only [R,I,sub_apply,ContinuousLinearMap.id_apply,lp.coeFn_sub,Pi.sub_apply,lp.single_apply,Pi.single_apply,if_pos]
  have hR : TotallyBounded (range R) := by
    apply LpSequence.totallyBounded_positive_operators_of_diagonal_tail_and_kernel_entries R (M+1) (by positivity)
      (fun n m => by
        rw [hrdiag]
        exact (norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add (hdiag n m) (le_refl (1:ℝ))))
      ?_ b κ hillFreeInteractionConstant hillFreeInteractionConstant_nonneg hκ ?_
    · intro ε hε
      obtain ⟨N,hN⟩ := P.sequenceJacobian_actual_real_uniform_diagonal_tail q hq hr ε hε
      exact ⟨N,fun n m hm => by rw [hrdiag]; exact hN n m hm⟩
    · intro n m r hrm
      have hb : ‖b m‖ = K*‖hillHminusGapWidthDisplacement ⟨q,hr⟩ m‖ := by
        simp only [b,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hK]
      have he : R n (lp.single 2 r 1) m = J n (lp.single 2 r 1) m := by
        simp only [R,I,sub_apply,ContinuousLinearMap.id_apply,lp.coeFn_sub,Pi.sub_apply,lp.single_apply,Pi.single_apply,if_neg hrm.symm,sub_zero]
      rw [he,hb,mul_comm K]
      exact hbound n m r hrm
  have himage : TotallyBounded ((fun S : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2 => S+I) '' range R) :=
    hR.image (uniformContinuous_id.add uniformContinuous_const)
  apply himage.subset
  rintro S ⟨n,rfl⟩
  exact ⟨R n,⟨n,rfl⟩,sub_add_cancel (J n) I⟩

theorem sequenceJacobian_actual_real_family_compact_closure (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    IsCompact (closure (range (fun n : ℕ+ => P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)))) :=
  (P.sequenceJacobian_actual_real_family_totallyBounded q hq hr).closure.isCompact_of_isClosed isClosed_closure

theorem exists_actual_real_uniform_operator_norm_bound (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ+, ‖P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)‖ ≤ M := by
  obtain ⟨M,hM⟩ := (P.sequenceJacobian_actual_real_family_totallyBounded q hq hr).isBounded.exists_norm_le
  exact ⟨max 0 M,le_max_left _ _,fun n => (hM _ ⟨n,rfl⟩).trans (le_max_right _ _)⟩

theorem exists_actual_real_sequenceJacobian_norm_convergent_subseq (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (f : ℕ → ℕ+) :
    ∃ T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun j => P.sequenceJacobian (f (σ j)) (hillHminusPsiZeroDisplacement (f (σ j)) ⟨q,hr⟩,q)) atTop (𝓝 T) := by
  obtain ⟨T,_,σ,hσ,hlim⟩ := (P.sequenceJacobian_actual_real_family_compact_closure q hq hr).isSeqCompact
    (fun j => subset_closure (show P.sequenceJacobian (f j) (hillHminusPsiZeroDisplacement (f j) ⟨q,hr⟩,q) ∈
      range (fun n => P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)) from ⟨f j,rfl⟩))
  exact ⟨T,σ,hσ,hlim⟩

end NLS.KdV.HillProductEquationPatch
