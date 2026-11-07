import NLS.KdV.HillPeriodJacobianClosureInverse
import NLS.SequenceSpaces.CompactInverseBound

/-! At EVERY original real source the ACTUAL FULL Hill period
Jacobians have ONE inverse operator-norm bound BEFORE ALL numerator
indices. The bound comes from invertibility of EVERY operator in their
compact norm closure, and retains both full inverse identities. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_actual_real_uniform_sequenceJacobian_equiv (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ+,
      ∃ e : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
        e.toContinuousLinearMap = P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) ∧
        ‖e.symm.toContinuousLinearMap‖ ≤ M := by
  let J (n : ℕ+) := P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)
  let K := closure (range J)
  have hK : IsCompact K := P.sequenceJacobian_actual_real_family_compact_closure q hq hr
  have hbij (x : K) : Function.Bijective x.val := P.sequenceJacobian_actual_real_closure_bijective q hq hr x.val x.property
  let e (x : K) : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2 :=
    ContinuousLinearEquiv.ofBijective x.val (LinearMap.ker_eq_bot.mpr (hbij x).1) (LinearMap.range_eq_top.mpr (hbij x).2)
  let Q (x : K) := x.val
  let R (x : K) := (e x).symm.toContinuousLinearMap
  have he (x : K) : (e x).toContinuousLinearMap = x.val := rfl
  have hQR (x : K) : (Q x).comp (R x) = ContinuousLinearMap.id ℂ _ := by
    change x.val.comp (e x).symm.toContinuousLinearMap = _
    rw [← he x]
    apply ContinuousLinearMap.ext
    intro a
    exact (e x).apply_symm_apply a
  have hRQ (x : K) : (R x).comp (Q x) = ContinuousLinearMap.id ℂ _ := by
    change (e x).symm.toContinuousLinearMap.comp x.val = _
    rw [← he x]
    apply ContinuousLinearMap.ext
    intro a
    exact (e x).symm_apply_apply a
  obtain ⟨M,hM,hbound⟩ := NLS.exists_uniform_inverse_norm_on_compact K hK Q R continuous_subtype_val hQR hRQ
  refine ⟨M,hM,?_⟩
  intro n
  let x : K := ⟨J n,subset_closure ⟨n,rfl⟩⟩
  exact ⟨e x,rfl,hbound x⟩

theorem exists_actual_real_uniform_sequenceJacobian_inverse (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ+,
      ∃ R : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
        (P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)).comp R = ContinuousLinearMap.id ℂ _ ∧
        R.comp (P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)) = ContinuousLinearMap.id ℂ _ ∧
        ‖R‖ ≤ M := by
  obtain ⟨M,hM,heq⟩ := P.exists_actual_real_uniform_sequenceJacobian_equiv q hq hr
  refine ⟨M,hM,?_⟩
  intro n
  obtain ⟨e,he,hbound⟩ := heq n
  refine ⟨e.symm.toContinuousLinearMap,?_,?_,hbound⟩
  · rw [← he]
    apply ContinuousLinearMap.ext
    intro a
    exact e.apply_symm_apply a
  · rw [← he]
    apply ContinuousLinearMap.ext
    intro a
    exact e.symm_apply_apply a

end NLS.KdV.HillProductEquationPatch
