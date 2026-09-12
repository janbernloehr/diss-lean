import NLS.SequenceSpaces.Weighted

/-!
# Multipliers between weighted coefficient spaces

A pointwise comparison of the weighted symbol gives a bounded linear map,
with the same constant, for every Banach exponent including infinity.
-/

noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A Fourier multiplier with a bound between its source and target weights. -/
def weightedMultiplier (w v : Weight) (m : ℤ → ℂ) (C : ℝ)
    (hm : ∀ n, v n * ‖m n‖ ≤ C * w n) (a : WeightedCoeff w p) :
    WeightedCoeff v p :=
  ⟨fun n => m n * a.val n, by
    apply ((lp.memℓp (weightEquiv w p a)).norm.const_mul C).mono
    intro n
    simp only [norm_mul, weightEquiv_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (v.positive n), abs_of_pos (w.positive n)]
    nlinarith [mul_le_mul_of_nonneg_right (hm n) (norm_nonneg (a.val n))]⟩

omit [Fact (1 ≤ p)] in
@[simp] theorem weightedMultiplier_apply (w v : Weight) (m : ℤ → ℂ) (C : ℝ)
    (hm : ∀ n, v n * ‖m n‖ ≤ C * w n) (a : WeightedCoeff w p) (n : ℤ) :
    (weightedMultiplier w v m C hm a).val n = m n * a.val n := rfl

theorem norm_weightedMultiplier_le (w v : Weight) (m : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ n, v n * ‖m n‖ ≤ C * w n) (a : WeightedCoeff w p) :
    ‖weightedMultiplier w v m C hm a‖ ≤ C * ‖a‖ := by
  have h : ‖weightEquiv v p (weightedMultiplier w v m C hm a)‖ ≤
      ‖(C : ℂ) • weightEquiv w p a‖ := by
    apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out))
    intro n
    change ‖(v n : ℂ) * (m n * a.val n)‖ ≤ ‖(C : ℂ) * ((w n : ℂ) * a.val n)‖
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC,
      abs_of_pos (v.positive n), abs_of_pos (w.positive n)]
    nlinarith [mul_le_mul_of_nonneg_right (hm n) (norm_nonneg (a.val n))]
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC,
    ← norm_eq] using h

/-- The bounded multiplier as a continuous linear map. -/
def weightedMultiplierCLM (w v : Weight) (m : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ n, v n * ‖m n‖ ≤ C * w n) : WeightedCoeff w p →L[ℂ] WeightedCoeff v p :=
  LinearMap.mkContinuous
    { toFun := weightedMultiplier w v m C hm
      map_add' := by intros; apply Subtype.ext; funext n; exact mul_add _ _ _
      map_smul' := by intros; apply Subtype.ext; funext n; exact mul_left_comm _ _ _ }
    C (norm_weightedMultiplier_le w v m C hC hm)

@[simp] theorem weightedMultiplierCLM_apply (w v : Weight) (m : ℤ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hm : ∀ n, v n * ‖m n‖ ≤ C * w n)
    (a : WeightedCoeff w p) (n : ℤ) :
    (weightedMultiplierCLM w v m C hC hm a).val n = m n * a.val n := rfl

/-- Monotone weights give a norm-decreasing inclusion preserving raw coefficients. -/
def inclusionCLM (w v : Weight) (h : ∀ n, v n ≤ w n) :
    WeightedCoeff w p →L[ℂ] WeightedCoeff v p :=
  weightedMultiplierCLM w v (fun _ => 1) 1 zero_le_one (by simpa using h)

@[simp] theorem inclusionCLM_apply (w v : Weight) (h : ∀ n, v n ≤ w n)
    (a : WeightedCoeff w p) (n : ℤ) : (inclusionCLM w v h a).val n = a.val n :=
  one_mul _

theorem norm_inclusionCLM_le (w v : Weight) (h : ∀ n, v n ≤ w n)
    (a : WeightedCoeff w p) : ‖inclusionCLM w v h a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using!
    norm_weightedMultiplier_le w v (fun _ => 1) 1 zero_le_one (by simpa using h) a

theorem inclusionCLM_injective (w v : Weight) (h : ∀ n, v n ≤ w n) :
    Function.Injective (inclusionCLM (p := p) w v h) := by
  intro a b hab
  apply Subtype.ext
  funext n
  simpa only [inclusionCLM_apply] using congrArg (fun c => c.val n) hab

end NLS.WeightedCoeff
