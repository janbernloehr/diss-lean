import NLS.SequenceSpaces.PositiveOneExtension
import NLS.SequenceSpaces.WeightedPositiveActionDerivatives

/-! The actual positive-frequency weighted ell1 space is isometric to
an enumerated ell1 model. Nonpositive raw slots are fixed to zero. -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.WeightedCoeff

def positiveActionLift (w : Weight) (e : ℤ ≃ ℕ+) : Coeff 1 →ₗᵢ[ℂ] WeightedCoeff w 1 :=
  (weightIsometry w 1).symm.toLinearIsometry.comp (positiveOneExtendIsometry e)

def positiveActionRestriction (w : Weight) (e : ℤ ≃ ℕ+) : WeightedCoeff w 1 →L[ℂ] Coeff 1 :=
  (positiveOneReindexPullCLM e).comp (weightIsometry w 1).toContinuousLinearEquiv.toContinuousLinearMap

theorem positiveActionLift_index (w : Weight) (e : ℤ ≃ ℕ+) (b : Coeff 1) (k : ℤ) :
    (positiveActionLift w e b).val (e k : ℤ)=b k/(w (e k : ℤ) : ℂ) := by
  change positiveOneExtendFunction e b (positiveIndexInjection e k)/(w (e k : ℤ) : ℂ)=_
  rw [positiveOneExtendFunction_index]

theorem positiveActionLift_nonpositive (w : Weight) (e : ℤ ≃ ℕ+) (b : Coeff 1)
    (j : ℤ) (hj : j≤0) : (positiveActionLift w e b).val j=0 := by
  change positiveOneExtendFunction e b j/(w j : ℂ)=0
  rw [positiveOneExtendFunction,dif_neg (by omega),zero_div]

theorem positiveActionRestriction_lift (w : Weight) (e : ℤ ≃ ℕ+) (b : Coeff 1) :
    positiveActionRestriction w e (positiveActionLift w e b)=b := by
  ext k
  change (w (e k : ℤ) : ℂ)*(positiveActionLift w e b).val (e k : ℤ)=b k
  rw [positiveActionLift_index,mul_div_cancel₀ _ (w.complex_ne_zero _)]

theorem positiveActionLift_mem_positiveActionLocus (w : Weight) (e : ℤ ≃ ℕ+)
    (b : Coeff 1) (hb : b∈Coeff.nonnegativeLocus 1) :
    positiveActionLift w e b∈positiveActionLocus w 1 := by
  refine ⟨(mem_nonnegativeLocus_iff w 1 _).mpr ?_,positiveActionLift_nonpositive w e b⟩
  have hw : weightEquiv w 1 (positiveActionLift w e b)=positiveOneExtendCoeff e b := by
    ext j
    change (w j : ℂ)*(positiveOneExtendFunction e b j/(w j : ℂ))=positiveOneExtendFunction e b j
    exact mul_div_cancel₀ _ (w.complex_ne_zero j)
  rw [hw]
  intro j
  change (positiveOneExtendFunction e b j).im=0 ∧ 0≤(positiveOneExtendFunction e b j).re
  rw [positiveOneExtendFunction]
  split_ifs with hj
  · exact hb _
  · exact ⟨rfl,le_rfl⟩

theorem positiveActionLift_restriction (w : Weight) (e : ℤ ≃ ℕ+)
    (a : WeightedCoeff w 1) (ha : ∀ j : ℤ, j≤0 → a.val j=0) :
    positiveActionLift w e (positiveActionRestriction w e a)=a := by
  apply Subtype.ext
  funext j
  by_cases hj : 0<j
  · let n : ℕ+ := ⟨j.toNat,by omega⟩
    have hn : (n : ℤ)=j := Int.toNat_of_nonneg hj.le
    have he : (e (e.symm n) : ℤ)=j := by rw [Equiv.apply_symm_apply,hn]
    rw [←he,positiveActionLift_index]
    change ((w (e (e.symm n) : ℤ) : ℂ)*a.val (e (e.symm n) : ℤ))/(w (e (e.symm n) : ℤ) : ℂ)=_
    rw [mul_div_cancel_left₀ _ (w.complex_ne_zero _)]
  · rw [positiveActionLift_nonpositive w e _ j (by omega),ha j (by omega)]

end NLS.WeightedCoeff
