import NLS.ZakharovShabat.SourceSection18HamiltonianCorrection
import NLS.ZakharovShabat.SourceSection28Original
import NLS.ZakharovShabat.SourceGapActionLowerBound

/-! # The omitted cutoff boundary in the proof of Theorem 23.4

The p.119 display includes |n|=N in the action sum but excludes it from
the gap sum. A small actual real source with only I_0 nonzero refutes
that display with the permitted cutoff N=0.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.ZakharovShabat

/-- A central action can be prescribed while controlling the exact physical H¹ norm. -/
theorem exists_realSobolev_small_central_action (t : ℝ) (ht : 0 < t) :
    ∃ a : realTypeSobolevSourceLocus,
      (∀ n : ℤ, sourceIndexedAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val) =
        if n = 0 then (t:ℂ) else 0) ∧
      0 < ‖sourcePhysicalH1Coordinates a.val‖^2 ∧
      ‖sourcePhysicalH1Coordinates a.val‖^2 ≤ 3*(t+t^2) ∧
      ∀ n : ℤ, n ≠ 0 → sourcePeriodicGapDisplacement (by simp) (by norm_num)
        (sobolevSourceInclusion a.val) n = 0 := by
  obtain ⟨a,ha,hm,_⟩ := exists_realSobolev_single_action 0 t ht.le
  have hi (n : ℤ) : sourceIndexedAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val) =
      if n = 0 then (t:ℂ) else 0 := by
    rw [sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num) n _ a.property,
      ← sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n _ a.property]
    exact ha n
  have hs (m : ℕ) : (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) m n) = t := by
    have he (n : ℤ) : sourceWeightedActionTerm (sourceH1RealSource a) m n =
        if n = 0 then t else 0 := by
      rw [sourceWeightedActionTerm]
      change (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*m)*
        ‖sourceRealAction (by simp) (by norm_num) (sobolevSourceInclusion a.val) a.property n‖ = _
      rw [← sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n _ a.property,ha n]
      by_cases hn : n = 0
      · subst n; simp [abs_of_pos ht]
      · simp [hn]
    simp only [he,tsum_ite_eq]
  have hb := sourceH1_third_norm_sq_le_actions a
  rw [hs 1,hs 0] at hb
  have hn : sourcePhysicalH1Coordinates a.val ≠ 0 := by
    intro hz
    have hi0 : sobolevSourceInclusion a.val = 0 := by
      rw [← normalizedWeightedSource_physicalH1Coordinates a.val,hz]
      apply (CoeffPair.toMax 2).injective
      apply Prod.ext <;> ext n <;> simp
    have h := ha 0
    rw [hi0,sourceComplexAction_eq_zero_at_zero] at h
    exact (Complex.ofReal_ne_zero.mpr ht.ne') (by simpa using h.symm)
  refine ⟨a,hi,sq_pos_of_pos (norm_pos_iff.mpr hn),by linarith,?_⟩
  intro n hn
  exact (sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
    n (sobolevSourceInclusion a.val) a.property).2.2.mp (by simp [hi n,hn])

/-- The exact p.119 weighted action and gap sums for a small one-gap source.
The inclusive sum keeps its positive central action; the strict gap tail is zero. -/
theorem exists_section28_small_tail_counterexample :
    ∃ a : realTypeSobolevSourceLocus,
      0 < 8*‖sourcePhysicalH1Coordinates a.val‖^2 ∧
      8*‖sourcePhysicalH1Coordinates a.val‖^2 ≤ 1 ∧
      (∑' n : ℤ, if 0 ≤ n.natAbs then
        (SpectralWeight.piSobolev 1 (by norm_num) (2*n))^2*
          ‖sourceIndexedAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val)‖ else 0) = 1/1000000 ∧
      (∑' n : ℤ, if 0 < n.natAbs then
        (SpectralWeight.piSobolev 1 (by norm_num) (2*n))^2*
          ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a.val) n‖^2 else 0) = 0 ∧
      4608*‖sourcePhysicalH1Coordinates a.val‖^2*
        (∑' n : ℤ, if 0 ≤ n.natAbs then
          (SpectralWeight.piSobolev 1 (by norm_num) (2*n))^2*
            ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a.val) n‖^2 else 0)
        < 1/1000000 := by
  obtain ⟨a,ha,hn,hb,hgap⟩ := exists_realSobolev_small_central_action (1/1000000) (by norm_num)
  have he (n : ℤ) :
      (SpectralWeight.piSobolev 1 (by norm_num) (2*n))^2*
        ‖sourceIndexedAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val)‖ =
      if n = 0 then (1/1000000:ℝ) else 0 := by
    rw [ha n]
    by_cases hn0 : n = 0
    · subst n; norm_num
    · simp [hn0]
  have hg0 : ‖sourcePeriodicGapDisplacement (by simp) (by norm_num)
      (sobolevSourceInclusion a.val) 0‖^2 ≤ 4*(1/1000000:ℝ) := by
    have h := source_gap_norm_sq_le_four_action (by simp) (by norm_num) (sourceH1RealSource a) 0
    change ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a.val) 0‖^2 ≤
      4*‖sourceComplexAction (by simp) (by norm_num) 0 (sobolevSourceInclusion a.val)‖ at h
    rw [sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) 0 _ a.property,
      ← sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num) 0 _ a.property,ha 0] at h
    norm_num only [ite_true,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 1/1000000)] at h
    convert h using 1
    norm_num
  have hg (n : ℤ) :
      (SpectralWeight.piSobolev 1 (by norm_num) (2*n))^2*
        ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a.val) n‖^2 =
      if n = 0 then ‖sourcePeriodicGapDisplacement (by simp) (by norm_num)
        (sobolevSourceInclusion a.val) 0‖^2 else 0 := by
    by_cases hn0 : n = 0
    · subst n; norm_num
    · rw [hgap n hn0]
      simp only [norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,if_neg hn0]
  refine ⟨a,by positivity,by norm_num at hb; linarith,?_,?_,?_⟩
  · simp only [Nat.zero_le,ite_true,he,tsum_ite_eq]
  · have hz (n : ℤ) : (if 0 < n.natAbs then
        (SpectralWeight.piSobolev 1 (by norm_num) (2*n))^2*
          ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a.val) n‖^2 else 0) = 0 := by
      by_cases hn0 : n = 0
      · subst n; simp
      · rw [hg n,if_neg hn0]
        simp
    simp only [hz,tsum_zero]
  · simp only [Nat.zero_le,ite_true,hg,tsum_ite_eq]
    have hmul := mul_le_mul_of_nonneg_left hg0
      (show 0 ≤ 4608*‖sourcePhysicalH1Coordinates a.val‖^2 by positivity)
    norm_num at hb
    nlinarith

namespace SourceSection28Data
variable {W₀ W V Wa B U T S : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}

/-- No retained original neighborhood validates the printed tail display,
already for the exact H¹ weight and the permitted cutoff N=0. -/
theorem not_printed_weighted_tail (Q : SourceSection28Data D A B U T S) :
    ¬ ∀ a : realTypeSobolevSourceLocus, sobolevSourceInclusion a.val ∈ S →
      0 < 8*‖sourcePhysicalH1Coordinates a.val‖^2 →
      8*‖sourcePhysicalH1Coordinates a.val‖^2 ≤ 1 →
      (∑' n : ℤ, if 0 ≤ n.natAbs then
        (SpectralWeight.piSobolev 1 (by norm_num) (2*n))^2*
          ‖sourceIndexedAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val)‖ else 0) ≤
      4608*‖sourcePhysicalH1Coordinates a.val‖^2*
        (∑' n : ℤ, if 0 < n.natAbs then
          (SpectralWeight.piSobolev 1 (by norm_num) (2*n))^2*
            ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a.val) n‖^2 else 0) := by
  obtain ⟨a,hpos,hsmall,hI,hstrict,_⟩ := exists_section28_small_tail_counterexample
  intro h
  have hx := h a (Q.action_gap_real_subset a.property) hpos hsmall
  rw [hI,hstrict] at hx
  norm_num at hx

/-- Restoring the cutoff boundary alone does not repair the omitted 1+ factor. -/
theorem not_weighted_tail_without_one (Q : SourceSection28Data D A B U T S) :
    ¬ ∀ a : realTypeSobolevSourceLocus, sobolevSourceInclusion a.val ∈ S →
      0 < 8*‖sourcePhysicalH1Coordinates a.val‖^2 →
      8*‖sourcePhysicalH1Coordinates a.val‖^2 ≤ 1 →
      (∑' n : ℤ, if 0 ≤ n.natAbs then
        (SpectralWeight.piSobolev 1 (by norm_num) (2*n))^2*
          ‖sourceIndexedAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val)‖ else 0) ≤
      4608*‖sourcePhysicalH1Coordinates a.val‖^2*
        (∑' n : ℤ, if 0 ≤ n.natAbs then
          (SpectralWeight.piSobolev 1 (by norm_num) (2*n))^2*
            ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a.val) n‖^2 else 0) := by
  obtain ⟨a,hpos,hsmall,hI,_,hfull⟩ := exists_section28_small_tail_counterexample
  intro h
  have hx := h a (Q.action_gap_real_subset a.property) hpos hsmall
  rw [hI] at hx
  exact (not_le_of_gt hfull) hx

end SourceSection28Data
end NLS.ZakharovShabat
