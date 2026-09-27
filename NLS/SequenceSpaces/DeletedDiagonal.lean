import NLS.SequenceSpaces.DeletedCoordinate
import NLS.SequenceSpaces.Multiplier

/-!
# Diagonal operators on the omitted-coordinate space

Lemma 12.6 separates the psi Jacobian into its nonzero diagonal and a
compact off-diagonal part. A bounded diagonal symbol with a bounded
pointwise inverse away from the omitted coordinate defines a bounded
linear equivalence on the omitted-coordinate coefficient space.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Coordinatewise multiplication, restricted to the coefficient
space whose `n`th entry is zero. -/
def deletedMultiplierCLM (n : ℤ) (d : Coeff ⊤) :
    DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
  ((multiplierCLM d).comp
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL)).codRestrict _
      (by
        intro a
        change d n * (a : Coeff p) n = 0
        have hn : (a : Coeff p) n = 0 := a.property
        rw [hn, mul_zero])

@[simp] theorem deletedMultiplierCLM_apply (n : ℤ) (d : Coeff ⊤)
    (a : DeletedCoeff p n) (m : ℤ) :
    ((deletedMultiplierCLM n d a : DeletedCoeff p n) : Coeff p) m =
      d m * (a : Coeff p) m := rfl

/-- Reciprocal symbols multiply to the identity on the retained
coordinates. -/
theorem deletedMultiplierCLM_inverse_left (n : ℤ) (d e : Coeff ⊤)
    (hde : ∀ m : ℤ, m ≠ n → d m * e m = 1)
    (a : DeletedCoeff p n) :
    deletedMultiplierCLM n e (deletedMultiplierCLM n d a) = a := by
  apply Subtype.ext
  ext m
  by_cases hmn : m = n
  · subst m
    have ha : (a : Coeff p) n = 0 := a.property
    simp [ha]
  · simp only [deletedMultiplierCLM_apply]
    calc
      e m * (d m * (a : Coeff p) m) =
          (d m * e m) * (a : Coeff p) m := by ring
      _ = (a : Coeff p) m := by rw [hde m hmn, one_mul]

/-- The same reciprocal identity in the other order. -/
theorem deletedMultiplierCLM_inverse_right (n : ℤ) (d e : Coeff ⊤)
    (hde : ∀ m : ℤ, m ≠ n → d m * e m = 1)
    (a : DeletedCoeff p n) :
    deletedMultiplierCLM n d (deletedMultiplierCLM n e a) = a := by
  apply Subtype.ext
  ext m
  by_cases hmn : m = n
  · subst m
    have ha : (a : Coeff p) n = 0 := a.property
    simp [ha]
  · simp only [deletedMultiplierCLM_apply]
    calc
      d m * (e m * (a : Coeff p) m) =
          (d m * e m) * (a : Coeff p) m := by ring
      _ = (a : Coeff p) m := by rw [hde m hmn, one_mul]

/-- A bounded reciprocal diagonal symbol yields a Banach-space
isomorphism on the deleted-coordinate space. -/
def deletedMultiplierEquiv (n : ℤ) (d e : Coeff ⊤)
    (hde : ∀ m : ℤ, m ≠ n → d m * e m = 1) :
    DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n where
  toLinearEquiv := {
    toFun := deletedMultiplierCLM n d
    invFun := deletedMultiplierCLM n e
    left_inv := deletedMultiplierCLM_inverse_left n d e hde
    right_inv := deletedMultiplierCLM_inverse_right n d e hde
    map_add' := (deletedMultiplierCLM n d).map_add
    map_smul' := (deletedMultiplierCLM n d).map_smul
  }
  continuous_toFun := (deletedMultiplierCLM n d).continuous
  continuous_invFun := (deletedMultiplierCLM n e).continuous

/-- A uniform positive lower bound on the retained diagonal entries
produces a bounded reciprocal symbol. -/
def inverseDeletedSymbol (n : ℤ) (d : Coeff ⊤)
    (c : ℝ) (hc : 0 < c)
    (hlower : ∀ m : ℤ, m ≠ n → c ≤ ‖d m‖) : Coeff ⊤ :=
  ⟨fun m => if m = n then 0 else (d m)⁻¹, by
    apply memℓp_infty
    refine ⟨c⁻¹, ?_⟩
    rintro _ ⟨m, rfl⟩
    by_cases hmn : m = n
    · simp [hmn, inv_nonneg.mpr hc.le]
    · simp only [if_neg hmn, norm_inv]
      exact (inv_le_inv₀ (hc.trans_le (hlower m hmn)) hc).2
        (hlower m hmn)⟩

@[simp] theorem inverseDeletedSymbol_apply (n : ℤ) (d : Coeff ⊤)
    (c : ℝ) (hc : 0 < c)
    (hlower : ∀ m : ℤ, m ≠ n → c ≤ ‖d m‖) (m : ℤ) :
    inverseDeletedSymbol n d c hc hlower m =
      if m = n then 0 else (d m)⁻¹ := rfl

/-- A bounded diagonal whose retained entries are bounded away from
zero is an isomorphism of the deleted-coordinate space. -/
def deletedMultiplierEquivOfLowerBound (n : ℤ) (d : Coeff ⊤)
    (c : ℝ) (hc : 0 < c)
    (hlower : ∀ m : ℤ, m ≠ n → c ≤ ‖d m‖) :
    DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n :=
  deletedMultiplierEquiv n d (inverseDeletedSymbol n d c hc hlower)
    (by
      intro m hmn
      rw [inverseDeletedSymbol_apply, if_neg hmn]
      have hm : d m ≠ 0 := by
        intro hz
        have h := hlower m hmn
        simp only [hz, norm_zero] at h
        exact (not_lt_of_ge h) hc
      exact mul_inv_cancel₀ hm)

end NLS.Coeff
