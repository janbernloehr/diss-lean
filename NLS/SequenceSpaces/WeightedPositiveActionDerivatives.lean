import NLS.ComplexAnalysis.ActionRayDerivative
import NLS.SequenceSpaces.WeightedNonnegativeActions
import NLS.SequenceSpaces.WeightedSingle

/-! # Intrinsic derivatives on the original positive-index action cone

Only positive-index action directions are determined by physical recovery.
The ambient negative and central slots are never used as action derivatives.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞)

/-- Actual nonnegative actions indexed by positive integers, with all other slots zero. -/
def positiveActionLocus : Set (WeightedCoeff w p) :=
  {a | a ∈ nonnegativeLocus w p ∧ ∀ n : ℤ, n ≤ 0 → a.val n = 0}

@[simp] theorem mem_positiveActionLocus (a : WeightedCoeff w p) :
    a ∈ positiveActionLocus w p ↔
      a ∈ nonnegativeLocus w p ∧ ∀ n : ℤ, n ≤ 0 → a.val n = 0 := Iff.rfl

/-- Zero actions, including every closed gap, belong to the original cone. -/
theorem zero_mem_positiveActionLocus : (0 : WeightedCoeff w p) ∈ positiveActionLocus w p :=
  ⟨zero_mem_nonnegativeLocus w p,by intro n _; rfl⟩

/-- Increasing one original positive action preserves the full cone. -/
theorem add_single_mem_positiveActionLocus (a : WeightedCoeff w p)
    (ha : a ∈ positiveActionLocus w p) (n : ℤ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    a+(t : ℂ) • single w n 1 ∈ positiveActionLocus w p := by
  constructor
  · intro j
    change (a.val j+(t : ℂ)*(single w n 1).val j).im = 0 ∧
      0 ≤ (a.val j+(t : ℂ)*(single w n 1).val j).re
    by_cases hj : j = n
    · subst j
      simp only [single_val,Pi.single_eq_same,mul_one,Complex.add_im,Complex.ofReal_im,
        Complex.add_re,Complex.ofReal_re,add_zero]
      exact ⟨(ha.1 n).1,add_nonneg (ha.1 n).2 ht⟩
    · simpa only [single_val,Pi.single_eq_of_ne hj,mul_zero,add_zero] using ha.1 j
  · intro j hj
    have hjn : j ≠ n := by omega
    change a.val j+(t : ℂ)*(single w n 1).val j = 0
    rw [single_val,Pi.single_eq_of_ne hjn,mul_zero,add_zero,ha.2 j hj]

/-- A physical positive action ray, extended constantly to negative parameters. -/
def positiveActionRay (a : positiveActionLocus w p) (n : ℕ+) (t : ℝ) : positiveActionLocus w p :=
  ⟨a.val+((max t 0 : ℝ) : ℂ) • single w (n : ℤ) 1,
    add_single_mem_positiveActionLocus w p a.val a.property n
      (by exact_mod_cast n.pos) (max t 0) (le_max_right _ _)⟩

theorem positiveActionRay_val_of_nonneg (a : positiveActionLocus w p) (n : ℕ+) (t : ℝ) (ht : 0 ≤ t) :
    (positiveActionRay w p a n t).val = a.val+(t : ℂ) • single w (n : ℤ) 1 := by
  change a.val+((max t 0 : ℝ) : ℂ) • single w (n : ℤ) 1 = _
  rw [max_eq_left ht]

@[simp] theorem positiveActionRay_zero (a : positiveActionLocus w p) (n : ℕ+) :
    positiveActionRay w p a n 0 = a := by
  apply Subtype.ext
  change a.val+((max (0 : ℝ) 0 : ℝ) : ℂ) • single w (n : ℤ) 1 = a.val
  simp

variable {w p} [Fact (1 ≤ p)]

/-- Recovery on actual actions determines every positive coordinate of the
actual complex Frechet differential, including at closed gaps. -/
theorem fderiv_single_eq_of_positive_action_recovery
    (f g : WeightedCoeff w p → ℂ) (a : WeightedCoeff w p)
    (ha : a ∈ positiveActionLocus w p) (n : ℤ) (hn : 0 < n)
    (hf : DifferentiableAt ℂ f a) (hg : DifferentiableAt ℂ g a)
    (he : ∀ b ∈ positiveActionLocus w p, f b = g b) :
    (fderiv ℂ f a) (single w n 1) = (fderiv ℂ g a) (single w n 1) :=
  NLS.ComplexAnalysis.fderiv_eq_of_positive_action_ray f g a _ hf hg
    (fun t ht => he _ (add_single_mem_positiveActionLocus w p a ha n hn t ht))

/-- Real physical values determine real positive action derivatives at every boundary point. -/
theorem fderiv_single_im_eq_zero_of_positive_action_recovery
    (f : WeightedCoeff w p → ℂ) (a : WeightedCoeff w p)
    (ha : a ∈ positiveActionLocus w p) (n : ℤ) (hn : 0 < n)
    (hf : DifferentiableAt ℂ f a)
    (he : ∀ b ∈ positiveActionLocus w p, (f b).im = 0) :
    ((fderiv ℂ f a) (single w n 1)).im = 0 :=
  NLS.ComplexAnalysis.fderiv_im_eq_zero_of_positive_action_ray f a _ hf
    (fun t ht => he _ (add_single_mem_positiveActionLocus w p a ha n hn t ht))

/-- Each unscaled raw coordinate of the derivative is analytic on the same
original action neighborhood. No bounded sequence-valued gradient is asserted. -/
theorem analyticOnNhd_fderiv_single (f : WeightedCoeff w p → ℂ)
    {U : Set (WeightedCoeff w p)} (hf : AnalyticOnNhd ℂ f U) (n : ℤ) :
    AnalyticOnNhd ℂ (fun a => (fderiv ℂ f a) (single w n 1)) U := by
  intro a ha
  exact ((ContinuousLinearMap.apply ℂ ℂ (single w n 1)).analyticAt _).comp (hf a ha).fderiv

end NLS.WeightedCoeff
