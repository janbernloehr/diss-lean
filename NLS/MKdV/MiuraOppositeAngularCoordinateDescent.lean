import NLS.MKdV.MiuraContinuousActionDescent
import NLS.FunctionalAnalysis.ScalarLinearODE

/-! # Oppositely rotating angular coordinates descend jointly to actions

The first factor is the actual positive NLS Cartesian coordinate, with
the orientation corresponding to the original restricted NLS angle. Any
independently specified continuous coordinate with the opposite action
rotation law gives an invariant product. Its global action/mean factor
exists even when other actions are closed and with infinite support.
This result does not construct the independent mKdV coordinate.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraNativeNLSAngularCoordinate (s m : ℕ) (a : MiuraRealSobolevSource s) : ℂ :=
  (miuraPositiveCartesianEval m (miuraSobolevNormalizedCartesianMap s a.val)).1-
    I*(miuraPositiveCartesianEval m (miuraSobolevNormalizedCartesianMap s a.val)).2

theorem continuous_miuraNativeNLSAngularCoordinate (s m : ℕ) :
    Continuous (miuraNativeNLSAngularCoordinate s m) := by
  have hM : Continuous (fun a : MiuraRealSobolevSource s => miuraSobolevNormalizedCartesianMap s a.val) := by
    have h := (miuraSobolevCartesianRealWeightEquiv s).continuous.comp
      (continuous_iff_continuousAt.mpr (fun a => (analyticAt_miuraPhysicalSobolevCartesianMap s a).continuousAt))
    exact (continuous_subtype_val.comp h).congr
      (fun a => miuraPhysicalSobolevNormalizedCartesianMap_inclusion s a)
  have he := (miuraPositiveCartesianEval m).continuous.comp hM
  exact (continuous_fst.comp he).sub (continuous_const.mul (continuous_snd.comp he))

theorem miuraNativeNLSAngularCoordinate_actionFlow (s m : ℕ) (_hm : 1 ≤ m)
    (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    miuraNativeNLSAngularCoordinate s m (miuraNativeRealActionFlow s a n t) =
      Complex.exp ((if m = n then I else 0)*(t : ℂ))*miuraNativeNLSAngularCoordinate s m a := by
  unfold miuraNativeNLSAngularCoordinate
  have he := miuraSobolevNormalizedCartesianMap_actionFlow s a.val (fun j => a.property j) n hn t
  change _ = _
  rw [show (miuraNativeRealActionFlow s a n t).val = miuraActionFlow s a.val (fun j => a.property j) n t from rfl,he,
    miuraCartesianRotation_eval]
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl,if_pos rfl]
    rw [mul_comm I (t : ℂ),Complex.exp_ofReal_mul_I]
    dsimp only [cartesianPlaneRotation]
    ring_nf
    simp only [I_sq]
    ring
  · have hne : (m : ℤ) ≠ (n : ℤ) := by exact_mod_cast hmn
    simp only [hne,hmn,if_false,zero_mul,Complex.exp_zero,one_mul]

/-- Opposite angular rotation laws suffice for the genuine global
product factorization through all physical actions and signed mean. -/
theorem exists_opposite_angular_product_action_factor (s : ℕ) (hs : 1 ≤ s)
    (m : ℕ) (hm : 1 ≤ m) (Q : MiuraRealSobolevSource s → ℂ) (hQ : Continuous Q)
    (hflow : ∀ a n, 1 ≤ n → ∀ t : ℝ, Q (miuraNativeRealActionFlow s a n t) =
      Complex.exp (-(if m = n then I else 0)*(t : ℂ))*Q a) :
    ∃ f : MiuraNativeActionMeanTarget s → ℂ, ∀ a : MiuraRealSobolevSource s,
      f (miuraNativeActionMeanMap s a.val) = miuraNativeNLSAngularCoordinate s m a*Q a := by
  apply exists_miuraContinuousObservable_action_factor s hs
    (fun a => miuraNativeNLSAngularCoordinate s m a*Q a)
    ((continuous_miuraNativeNLSAngularCoordinate s m).mul hQ)
  intro a n hn t
  rw [miuraNativeNLSAngularCoordinate_actionFlow s m hm a n hn t,hflow a n hn t]
  have hc : Complex.exp ((if m = n then I else 0)*(t : ℂ))*
      Complex.exp (-(if m = n then I else 0)*(t : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    rw [← add_mul,add_neg_cancel,zero_mul,Complex.exp_zero]
  linear_combination (miuraNativeNLSAngularCoordinate s m a*Q a)*hc

end NLS.MKdV
