import NLS.SequenceSpaces.NonnegativeActions
import NLS.SequenceSpaces.Weighted

/-! # Real quadratic lifts with the exact squared native weight -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
local instance : (2 : ℝ≥0∞).HolderTriple 2 1 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

/-- A nonnegative action sequence with squared weight has real coordinate
lifts with the original weight, including arbitrary infinite zero sets. -/
theorem exists_real_quadratic_lift (w v : Weight) (hv : ∀ n, v n = w n*w n)
    (J : WeightedCoeff v 1) (hJ : ∀ n, (J.val n).im = 0 ∧ 0 ≤ (J.val n).re) :
    ∃ x y : WeightedCoeff w 2, (∀ n, (x.val n).im = 0 ∧ (y.val n).im = 0) ∧
      ∀ n, (1/2 : ℂ)*(x.val n^2+y.val n^2) = J.val n := by
  let b := weightIsometry v 1 J
  have hb : b ∈ Coeff.nonnegativeLocus 1 := by
    intro n
    change (((v n : ℂ)*J.val n).im = 0) ∧ 0 ≤ ((v n : ℂ)*J.val n).re
    simp only [Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      (hJ n).1,mul_zero,zero_mul,add_zero,sub_zero]
    exact ⟨trivial,mul_nonneg (v.positive n).le (hJ n).2⟩
  obtain ⟨u,hu,hact,_⟩ := Coeff.exists_real_quadraticActions_lift (p := 2) (by simp) b hb
  let x := (weightIsometry w 2).symm u.1
  let y := (weightIsometry w 2).symm u.2
  refine ⟨x,y,?_,?_⟩
  · intro n
    change (u.1 n/(w n : ℂ)).im = 0 ∧ (u.2 n/(w n : ℂ)).im = 0
    simp [Complex.div_im,hu.1 n,hu.2 n]
  · intro n
    have he := congrArg (fun q : Coeff 1 => q n) hact
    rw [quadraticActionsExponent_apply] at he
    change (u.1 n^2+u.2 n^2)/2 = (v n : ℂ)*J.val n at he
    have hw : (v n : ℂ) = (w n : ℂ)^2 := by rw [hv]; push_cast; ring
    rw [hw] at he
    change (1/2 : ℂ)*((u.1 n/(w n : ℂ))^2+(u.2 n/(w n : ℂ))^2) = J.val n
    apply mul_left_cancel₀ (pow_ne_zero 2 (w.complex_ne_zero n))
    calc
      _ = (u.1 n^2+u.2 n^2)/2 := by field_simp [w.complex_ne_zero n]
      _ = _ := he

end NLS.WeightedCoeff
