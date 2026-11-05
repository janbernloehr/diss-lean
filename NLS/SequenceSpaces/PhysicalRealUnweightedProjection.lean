import NLS.SequenceSpaces.PhysicalRealUnweightedCoefficients

/-! # A bounded projection onto the original physical real coefficient form -/
noncomputable section
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS.Coeff
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

def conjugateReflectionRealCLM : Coeff p →L[ℝ] Coeff p :=
  LinearMap.mkContinuous
    { toFun := fun a => star (reflection a)
      map_add' := by intro a b; ext n; simp
      map_smul' := by
        intro r a
        ext n
        change conj ((r : ℂ)*a (-n)) = (r : ℂ)*conj (a (-n))
        rw [map_mul,Complex.conj_ofReal] }
    1 (by intro a; change ‖star (reflection a)‖ ≤ 1*‖a‖; rw [norm_star,reflection.norm_map,one_mul])

@[simp] theorem conjugateReflectionRealCLM_apply (a : Coeff p) (n : ℤ) :
    conjugateReflectionRealCLM p a n = conj (a (-n)) := rfl

def physicalRealPart : Coeff p →L[ℝ] physicalRealSubmodule p :=
  ((1/2 : ℝ) • (ContinuousLinearMap.id ℝ (Coeff p)+conjugateReflectionRealCLM p)).codRestrict
    (physicalRealSubmodule p) (by
      intro a n
      change ((1/2 : ℝ) : ℂ)*(a n+conj (a (-n))) =
        conj (((1/2 : ℝ) : ℂ)*(a (-n)+conj (a (-(-n)))))
      rw [map_mul,map_add,Complex.conj_ofReal,Complex.conj_conj,neg_neg]
      ring)

theorem physicalRealPart_apply (a : Coeff p) (n : ℤ) :
    (physicalRealPart p a).val n = (a n+conj (a (-n)))/2 := by
  change ((1/2 : ℝ) : ℂ)*(a n+conj (a (-n))) = _
  push_cast
  ring

theorem physicalRealPart_real (a : physicalRealSubmodule p) : physicalRealPart p a.val = a := by
  apply Subtype.ext
  ext n
  rw [physicalRealPart_apply,← a.property n]
  ring

end NLS.Coeff
