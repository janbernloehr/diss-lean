import NLS.ZakharovShabat.SourceHilbertActionReductionFiniteGap

/-! # Weighted actions along the physical action-reduction curve

Before the selected action collapses, only that action changes, at unit
speed. Every weighted finite-gap action sum therefore has an exact affine
formula, without any growth restriction on the weights.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The full complex action changes by minus the parameter at precisely
the selected index. -/
theorem hilbertActionReduction_complexAction
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n k : ℤ)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re)
    (t : ℝ) (ht : t ≤ (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re) :
    sourceComplexAction (by simp) (by norm_num) k (D.hilbertActionReduction φ n t).val =
      sourceComplexAction (by simp) (by norm_num) k φ.val - if k = n then (t : ℂ) else 0 := by
  rw [sourceComplexAction_eq_sourceRealAction _ _ _ _ (D.hilbertActionReduction φ n t).property,
    sourceComplexAction_eq_sourceRealAction _ _ _ _ φ.property]
  have himψ := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
    (D.hilbertActionReduction φ n t).val (D.hilbertActionReduction φ n t).property k).2.1
  have himφ := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
    φ.val φ.property k).2.1
  by_cases hkn : k = n
  · subst k
    apply Complex.ext
    · simpa using D.hilbertActionReduction_action_same φ n ha t ht
    · simp [himψ,himφ]
  · simp only [if_neg hkn,sub_zero]
    exact Complex.ext (D.hilbertActionReduction_action_ne φ n k hkn t) (himψ.trans himφ.symm)

/-- Arbitrary weighted finite-gap action sums decrease by weight times time. -/
theorem hilbertActionReduction_weighted_actions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re)
    (w : ℤ → ℂ) (t : ℝ)
    (ht : t ≤ (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re) :
    (∑' k : ℤ, w k * sourceComplexAction (by simp) (by norm_num) k (D.hilbertActionReduction φ n t).val) =
      (∑' k : ℤ, w k * sourceComplexAction (by simp) (by norm_num) k φ.val) - w n * (t : ℂ) := by
  classical
  have hsum (ψ : realTypeSourceSubmodule 2)
      (hS : ∀ k ∉ hf.toFinset, canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) k = 0) :
      (∑' k : ℤ, w k * sourceComplexAction (by simp) (by norm_num) k ψ.val) =
        ∑ k ∈ hf.toFinset, w k * sourceComplexAction (by simp) (by norm_num) k ψ.val := by
    apply tsum_eq_sum
    intro k hk
    rw [sourceComplexAction_eq_sourceRealAction _ _ _ _ ψ.property,
      (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) ψ.val ψ.property k).2.2.mpr
        (by simpa only [sourcePeriodicGapDisplacement_apply] using hS k hk),mul_zero]
  rw [hsum _ (D.hilbertActionReduction_gap_support φ hf n hn t),hsum φ (by
    intro k hk
    by_contra hne
    exact hk (hf.mem_toFinset.mpr hne))]
  simp_rw [D.hilbertActionReduction_complexAction φ n _ ha t ht,mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',if_pos (hf.mem_toFinset.mpr hn)]

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
