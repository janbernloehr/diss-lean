import NLS.KdV.HillProductEquationKernelInjectivity
import NLS.KdV.HillProductEquationFredholmAlternative

/-! The ACTUAL full real Hill period Jacobian is a Banach isomorphism
at every real native source and every fixed numerator index. -/
noncomputable section
open Complex
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem sequenceJacobian_actual_real_bijective (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    Function.Bijective (P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)) :=
  P.sequenceJacobian_actual_real_bijective_of_injective q hq hr n
    (P.sequenceJacobian_actual_real_injective n q hq hr)

theorem exists_actual_real_sequenceJacobian_equiv (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ e : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
      e.toContinuousLinearMap = P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) := by
  have hbij := P.sequenceJacobian_actual_real_bijective n q hq hr
  exact ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hbij.1)
    (LinearMap.range_eq_top.mpr hbij.2),rfl⟩

theorem exists_actual_real_sequenceJacobian_inverse (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ R : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
      (P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)).comp R = ContinuousLinearMap.id ℂ _ ∧
      R.comp (P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)) = ContinuousLinearMap.id ℂ _ := by
  obtain ⟨e,he⟩ := P.exists_actual_real_sequenceJacobian_equiv n q hq hr
  refine ⟨e.symm.toContinuousLinearMap,?_,?_⟩
  · rw [← he]
    apply ContinuousLinearMap.ext
    intro a
    exact e.apply_symm_apply a
  · rw [← he]
    apply ContinuousLinearMap.ext
    intro a
    exact e.symm_apply_apply a

end NLS.KdV.HillProductEquationPatch
