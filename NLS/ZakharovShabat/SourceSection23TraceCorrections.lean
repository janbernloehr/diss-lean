import NLS.ZakharovShabat.SourceIndexedHigherActionAnalytic
import NLS.ZakharovShabat.SourceRealHigherActionPositive
import NLS.ZakharovShabat.SourceSection18HamiltonianCorrection
import NLS.ZakharovShabat.SobolevQuarticMassBound
import NLS.ZakharovShabat.SourceSobolevHigherActionTrace

/-! # Actual-source counterexamples to the Section 23 trace outline

The trace sums over every integer index and has a positive factor 4ᵐ.
Two independent finite-gap examples refute the p. 105 index restriction
and alternating sign, using the original higher-action definition.
-/
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- The positive-index trace in the p. 105 outline fails on an actual unit-action source. -/
theorem section23_positiveIndex_trace_counterexample :
    ∃ a : realTypeSobolevSourceLocus,
      (∀ k : ℕ, (∑' n : {n : ℤ // 1 ≤ n}, sourceIndexedHigherAction
        (by simp) (by norm_num) n.val k (sobolevSourceInclusion a.val)) = 0) ∧
      (periodOneSobolevHamiltonian a.val).re ≥ 1 ∧
      (∑' n : {n : ℤ // 1 ≤ n}, sourceIndexedHigherAction
        (by simp) (by norm_num) n.val 2 (sobolevSourceInclusion a.val)) ≠
          periodOneSobolevHamiltonian a.val/4 := by
  obtain ⟨a,ha,hm,_⟩ := exists_realSobolev_single_action 0 1 (by norm_num)
  let φ : realTypeSourceSubmodule 2 := ⟨sobolevSourceInclusion a.val,a.property⟩
  have hc (n : ℤ) (hn : n ≠ 0) : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
    have hz : sourceComplexAction (by simp) (by norm_num) n φ.val = 0 := by
      change sourceComplexAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val) = 0
      simp [ha n,hn]
    have he := (sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero
      (by simp) (by norm_num) n φ.val φ.property).2.2.mp hz
    simpa only [sourcePeriodicGapDisplacement_apply] using he
  have hs (k : ℕ) : (∑' n : {n : ℤ // 1 ≤ n}, sourceIndexedHigherAction
      (by simp) (by norm_num) n.val k (sobolevSourceInclusion a.val)) = 0 := by
    trans ∑' _ : {n : ℤ // 1 ≤ n}, (0:ℂ)
    swap
    · simp
    apply tsum_congr
    intro n
    change sourceIndexedHigherAction (by simp) (by norm_num) n.val k φ.val = 0
    rw [sourceIndexedHigherAction_eq_real,sourceRealHigherAction_of_collapsed
      (by simp) (by norm_num) φ n.val (hc n.val (by have := n.property; omega)) k]
    rfl
  have he : 1 ≤ (periodOneSobolevHamiltonian a.val).re := by
    have hq := periodOneSobolevMass_sq_le_quartic a
    rw [hm] at hq
    rw [periodOneSobolevHamiltonian,Complex.add_re,periodOneSobolevKinetic_real_eq]
    norm_num only [Complex.ofReal_one,Complex.one_re,one_pow,
      ← Complex.ofReal_pow,Complex.ofReal_re] at hq ⊢
    nlinarith [sq_nonneg ‖periodOneDerivative a.val.1‖]
  refine ⟨a,hs,he,?_⟩
  rw [hs]
  intro hz
  have hz' : periodOneSobolevHamiltonian a.val = 0 := (div_eq_zero_iff.mp hz.symm).resolve_right (by norm_num)
  rw [hz'] at he
  norm_num at he

/-- Even after restoring all integer indices, the printed alternating sign fails at H₅. -/
theorem section23_alternating_trace_counterexample :
    ∃ φ : realTypeSourceSubmodule 2, ∃ hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num),
      0 < (sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 5).re ∧
      (∑' n : ℤ, sourceIndexedHigherAction (by simp) (by norm_num) n 4 φ.val) ≠
        -sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 5/16 := by
  obtain ⟨a,ha,_,_⟩ := exists_realSobolev_single_action 0 1 (by norm_num)
  let φ : realTypeSourceSubmodule 2 := ⟨sobolevSourceInclusion a.val,a.property⟩
  have hclosed (n : ℤ) (hn : n ≠ 0) : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
    have hz : sourceComplexAction (by simp) (by norm_num) n φ.val = 0 := by
      change sourceComplexAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val) = 0
      simp [ha n,hn]
    have he := (sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero
      (by simp) (by norm_num) n φ.val φ.property).2.2.mp hz
    simpa only [sourcePeriodicGapDisplacement_apply] using he
  have hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
    apply (Set.finite_singleton (0:ℤ)).subset
    intro n hn
    by_contra hn0
    exact hn (hclosed n hn0)
  have hopen : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 ≠ 0 := by
    intro hz
    have he := (sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero
      (by simp) (by norm_num) 0 φ.val φ.property).2.2.mpr
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hz)
    change sourceComplexAction (by simp) (by norm_num) 0 (sobolevSourceInclusion a.val) = 0 at he
    rw [ha 0] at he
    norm_num at he
  have hs : (∑' n : ℤ, (sourceRealHigherAction (by simp) (by norm_num) φ n 4 : ℂ)) =
      (sourceRealHigherAction (by simp) (by norm_num) φ 0 4 : ℂ) := by
    apply tsum_eq_single 0
    intro n hn
    rw [sourceRealHigherAction_of_collapsed (by simp) (by norm_num) φ n (hclosed n hn) 4]
    rfl
  have hp := sourceRealHigherAction_even_pos (by simp) (by norm_num) φ 0 2 hopen
  have ht := sourceFiniteGap_tsum_higherActions_eq_hamiltonian (by simp) (by norm_num) φ hf 4
  norm_num only [Nat.reduceAdd,pow_succ,pow_zero,mul_one] at ht
  have hnorm : (sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 5).re =
      16*sourceRealHigherAction (by simp) (by norm_num) φ 0 4 := by
    rw [hs] at ht
    have ht' := (eq_div_iff (by norm_num : (16:ℂ) ≠ 0)).mp ht
    have he := congrArg Complex.re ht'
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im] at he
    norm_num at he
    linarith
  refine ⟨φ,hf,by rw [hnorm]; positivity,?_⟩
  simp_rw [sourceIndexedHigherAction_eq_real (by simp) (by norm_num) φ]
  rw [ht]
  intro he
  have hz : sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 5 = 0 := by
    linear_combination (8:ℂ)*he
  rw [hz] at hnorm
  norm_num at hnorm
  linarith

end NLS.ZakharovShabat
