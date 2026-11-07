import NLS.SequenceSpaces.WeightedPositiveActionSpace
import NLS.SequenceSpaces.RealCoefficientCoordinates

/-! The original positive-frequency weighted action cone and its REAL
Banach space, with exact isometric coefficient coordinates. -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.WeightedCoeff

abbrev PositiveSupportedActionCone (w : Weight) :=
  {a : positiveSupportedSubmodule w | a.val∈nonnegativeLocus w 1}

def positiveActionConeZero (w : Weight) : PositiveSupportedActionCone w :=
  ⟨0,zero_mem_nonnegativeLocus w 1⟩

def positiveActionConeHomeomorph (w : Weight) (e : ℤ ≃ ℕ+) :
    PositiveSupportedActionCone w ≃ₜ Coeff.nonnegativeLocus 1 :=
  (positiveActionModelEquiv w e).symm.toHomeomorph.subtype (positiveActionModelEquiv_nonnegative w e)

@[simp] theorem positiveActionConeHomeomorph_apply (w : Weight) (e : ℤ ≃ ℕ+)
    (a : PositiveSupportedActionCone w) :
    (positiveActionConeHomeomorph w e a).val=(positiveActionModelEquiv w e).symm a.val := rfl

theorem normalized_positive_action_real_iff (w : Weight) (e : ℤ ≃ ℕ+)
    (a : positiveSupportedSubmodule w) :
    (positiveActionModelEquiv w e).symm a∈Coeff.realLocus 1 ↔ ∀ j : ℤ, (a.val.val j).im=0 := by
  constructor
  · intro h j
    by_cases hj : 0<j
    · let n : ℕ+ := ⟨j.toNat,by omega⟩
      have hn : (n : ℤ)=j := Int.toNat_of_nonneg hj.le
      have he : (e (e.symm n) : ℤ)=j := by rw [Equiv.apply_symm_apply,hn]
      have hh := h (e.symm n)
      change ((w (e (e.symm n) : ℤ) : ℂ)*a.val.val (e (e.symm n) : ℤ)).im=0 at hh
      rw [he] at hh
      simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt (w.positive j))
    · rw [a.property j (by omega)]
      rfl
  · intro h k
    change ((w (e k : ℤ) : ℂ)*a.val.val (e k : ℤ)).im=0
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,h (e k : ℤ),
      zero_mul,mul_zero,add_zero]

theorem mem_positive_action_coordinateRealSubmodule_iff (w : Weight) (e : ℤ ≃ ℕ+)
    (a : positiveSupportedSubmodule w) :
    a∈Coeff.coordinateRealSubmodule (positiveActionModelEquiv w e).symm.toContinuousLinearEquiv ↔
      ∀ j : ℤ, (a.val.val j).im=0 := by
  change (positiveActionModelEquiv w e).symm a∈Coeff.realLocus 1 ↔ _
  exact normalized_positive_action_real_iff w e a

end NLS.WeightedCoeff
