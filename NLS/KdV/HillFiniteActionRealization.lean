import NLS.KdV.HillOriginalBirkhoffMap
import NLS.KdV.HillHminusPhysicalArnoldActions

/-! # Actual mean-zero physical realization of finite nonnegative Hill actions -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.KdV

/-- Finite canonical real coordinates, normalized in the original physical
Hilbert target. The index `k` represents the physical gap `k+1`. -/
def hillFiniteActionTarget (a : ℕ → ℝ) (s : Finset ℕ) : HillBirkhoffSpace :=
  (RealWeightedNatPair.normalizationEquiv _ _).symm
    (∑ k ∈ s, lp.single 2 k
      ((hillBirkhoffBaseWeight k : ℂ)*(Real.sqrt (2*a k) : ℂ)))

theorem hillFiniteActionTarget_apply (a : ℕ → ℝ) (s : Finset ℕ) (k : ℕ) :
    (hillFiniteActionTarget a s).val k =
      (if k ∈ s then Real.sqrt (2*a k) else 0, 0) := by
  classical
  unfold hillFiniteActionTarget
  have he : (∑ j ∈ s, lp.single 2 j
      ((hillBirkhoffBaseWeight j : ℂ)*(Real.sqrt (2*a j) : ℂ))) k =
      (hillBirkhoffBaseWeight k : ℂ)*
        ((if k ∈ s then Real.sqrt (2*a k) else 0 : ℝ) : ℂ) := by
    rw [lp.coeFn_sum]
    simp only [Finset.sum_apply, lp.single_apply]
    by_cases hk : k ∈ s <;> simp [hk]
  have h := RealWeightedNatPair.normalization_symm_apply_of_mul
    hillBirkhoffBaseWeight hillBirkhoffBaseWeight_pos _ k _ he
  simpa using h

/-- Every finite nonnegative action prescription is attained by an actual
original real mean-zero L2 source, including every prescribed closed gap. -/
theorem exists_hillOriginalSource_finite_actions (a : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (s : Finset ℕ) :
    ∃ q : hillRealMeanZeroSourceSubmodule, ∀ k : ℕ,
      hillRealGapIntegral q.val.val q.val.property.1 q.val.property.2 (k+1) 0 =
        if k ∈ s then a k else 0 := by
  classical
  refine ⟨hillOriginalBirkhoffInverse (hillFiniteActionTarget a s), ?_⟩
  intro k
  have h := hillOriginalBirkhoffMap_action_identity
    (hillOriginalBirkhoffInverse (hillFiniteActionTarget a s)) k
  rw [hillOriginalBirkhoffMap_apply_inverse, hillFiniteActionTarget_apply] at h
  dsimp only at h
  by_cases hk : k ∈ s
  · have hs : (Real.sqrt (2*a k))^2 = 2*a k :=
      Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (ha k))
    simp only [if_pos hk, hs,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at h
    rw [if_pos hk]
    linarith
  · simp only [if_neg hk, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at h
    rw [if_neg hk]
    linarith

end NLS.KdV
