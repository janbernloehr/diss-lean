import NLS.MKdV.MiuraCentralHalfTurn
import NLS.MKdV.MiuraL2ZeroActionRigidity
import NLS.MKdV.MiuraConstantActions

/-! # The central half turn reverses the literal real constants -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.Poisson
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraRealConstant (r : ℝ) : MiuraRealL2 :=
  ⟨lp.single 2 0 (r : ℂ),by
    intro j
    by_cases hj : j = 0 <;> simp [lp.single_apply,hj]⟩

@[simp] theorem miuraRealConstant_apply (r : ℝ) (j : ℤ) :
    (miuraRealConstant r).val j = if j = 0 then (r : ℂ) else 0 := by
  change (lp.single (E := fun _ : ℤ => ℂ) 2 0 (r : ℂ)) j = _
  simp [lp.single_apply,Pi.single_apply]

@[simp] theorem miuraRealConstant_mean (r : ℝ) : (miuraRealConstant r).val 0 = (r : ℂ) := by simp

theorem miuraRealConstant_H1 (r : ℝ) :
    scalarInclusion (scalarMode (p := 2) 0 (r : ℂ)) = (miuraRealConstant r).val :=
  scalarInclusion_scalarMode 0 (r : ℂ)

theorem scalarMode_zero_real (r : ℝ) :
    ∀ j, (scalarMode (p := 2) 0 (r : ℂ)).val j = conj ((scalarMode (p := 2) 0 (r : ℂ)).val (-j)) := by
  intro j
  by_cases hj : j = 0 <;> simp [scalarMode_apply,hj]

theorem miuraRealConstant_physical_actionSequence (r : ℝ) : miuraL2ActionSequence (miuraRealConstant r).val = 0 := by
  let u : ScalarDomain 2 := scalarMode 0 (r : ℂ)
  have hu := scalarMode_zero_real r
  have hdu : periodOneDerivative u = 0 := by
    ext j
    rw [periodOneDerivative_apply,scalarMode_apply]
    by_cases hj : j = 0 <;> simp [hj]
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraL2ActionSequence_domain
  apply Subtype.ext
  funext n
  by_cases hn : 0 < n
  · have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
    have hnN : 1 ≤ n.toNat := by omega
    rw [← hi,hcoord _ (hreal (miuraRealConstant r).property) n.toNat hnN,
      ← miuraRealConstant_H1,miuraL2Action_eq_physical u hu n.toNat hnN,
      miuraMKdVAction_eq_zero_of_derivative_zero u hu hdu n.toNat hnN]
    rfl
  · rw [miuraL2ActionSequence_nonpositive _ n hn]
    rfl

theorem miuraRealConstant_central_action_ne_zero (r : ℝ) (hr : r ≠ 0) :
    miuraOriginalNLSActionSequence (miuraRealConstant r).val 0 ≠ 0 := by
  let u : ScalarDomain 2 := scalarMode 0 (r : ℂ)
  have hu := scalarMode_zero_real r
  intro hz
  rw [miuraOriginalNLSActionSequence_apply _ (real_mem_miuraOriginalNLSActionDomain _ (miuraRealConstant r).property),
    ← miuraRealConstant_H1] at hz
  change miuraRestrictedNLSAction 0 (scalarInclusion u) = 0 at hz
  rw [miuraRestrictedNLSAction_eq_original u hu] at hz
  have hmean := (miuraNLSAction_zero_iff_mean_zero u hu).mp hz
  change (scalarMode (p := 2) 0 (r : ℂ)).val 0 = 0 at hmean
  have hzero : r = 0 := by simpa only [scalarMode_apply,ite_true,Complex.ofReal_eq_zero] using hmean
  exact hr hzero

/-- The literal mean of every constant is reversed by the actual central
NLS half turn. The zero constant is included. -/
theorem miuraCentralHalfTurn_constant_mean (r : ℝ) :
    (miuraCentralHalfTurn (miuraRealConstant r)).val 0 = -(r : ℂ) := by
  have hs := miuraCentralHalfTurn_mean_square (miuraRealConstant r)
  rw [miuraRealConstant_mean] at hs
  by_cases hr : r = 0
  · subst r
    simp only [Complex.ofReal_zero,zero_pow (by norm_num : 2 ≠ 0)] at hs
    simpa only [Complex.ofReal_zero,neg_zero] using sq_eq_zero_iff.mp hs
  have hJ : miuraL2ActionSequence (miuraCentralHalfTurn (miuraRealConstant r)).val = 0 :=
    (miuraCentralHalfTurn_physical_actionSequence _).trans (miuraRealConstant_physical_actionSequence r)
  have hconst := eq_single_mean_of_miuraL2ActionSequence_zero
    (miuraCentralHalfTurn (miuraRealConstant r)).val (miuraCentralHalfTurn (miuraRealConstant r)).property hJ
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hp | hn
  · have hfixed : miuraCentralHalfTurn (miuraRealConstant r) = miuraRealConstant r := by
      apply Subtype.ext
      change (miuraCentralHalfTurn (miuraRealConstant r)).val = lp.single 2 0 (r : ℂ)
      simpa only [hp] using hconst
    exact False.elim (miuraRealConstant_central_action_ne_zero r hr
      ((miuraCentralHalfTurn_eq_self_iff_central_action_zero _).mp hfixed))
  · exact hn

end NLS.MKdV
