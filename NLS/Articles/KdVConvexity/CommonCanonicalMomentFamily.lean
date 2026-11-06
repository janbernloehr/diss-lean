import NLS.Articles.KdVConvexity.CanonicalMomentPreparation
import NLS.KdV.HillHminusOneCanonicalHighPeriods
import NLS.KdV.HillHminusOneArnoldActionComparison

/-! # A common analytic family of all actual canonical H^-1 moments

The finite analytic head and the literal uniform high source family are
combined on one complex potential neighborhood. They agree with every
actual real canonical period, retain all signs and zero criteria, and
satisfy the uniform quadratic weighted cubic bound throughout the tail.
Global Birkhoff-action identification is a separate obligation.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

/-- The actual all-index potential-space input for analytic action descent:
one neighborhood precedes every index, polynomial order and tail bound. -/
theorem exists_common_analytic_canonical_moment_family
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ W : Set PeriodOneHminusOne,
      0 < C ∧ 2 ≤ N ∧ IsOpen W ∧ q ∈ W ∧
      ∃ A : ℕ+ → ℕ → PeriodOneHminusOne → ℂ, ∃ R : ℕ+ → PeriodOneHminusOne → ℂ,
        (∀ n m, AnalyticOnNhd ℂ (A n m) W) ∧ (∀ n, AnalyticOnNhd ℂ (R n) W) ∧
        (∀ n : ℕ+, N ≤ (n : ℕ) → ∀ p : PeriodOneHminusOne,
          (∀ m, A n m p = hillHminusHighContourMoment (n : ℕ) m p) ∧
          R n p = hillHminusHighCubicContourMoment (n : ℕ) p) ∧
        (∀ n : ℕ+, N ≤ (n : ℕ) → ∀ p ∈ W,
          ‖((8*(n : ℕ)*Real.pi : ℝ) : ℂ)*R n p‖ ≤ C*‖A n 0 p‖^2) ∧
        ∀ p ∈ W, ∀ hp : IsRealPeriodOneHminusOne p, ∀ n : ℕ+,
          (∀ m, A n m p = hillHminusRealGapContourMoment p hp n m) ∧
          R n p = hillHminusRealGapCubicContourMoment p hp n ∧
          0 ≤ (A n 0 p).re ∧ (R n p).re ≤ 0 ∧ (R n p).im = 0 ∧
          (R n p = 0 ↔ A n 0 p = 0) := by
  classical
  obtain ⟨Nt,Vt,hNt,hVt,hqt,hmatch⟩ := exists_hillHminus_canonical_high_period_agreement q
  obtain ⟨C,Nb,Vb,hC,_,hVb,hqb,hbound⟩ := exists_analytic_hillHminus_moments_with_action_bounds q
  obtain ⟨Na,Va,_,hVa,hqa,hanalytic⟩ := exists_analytic_hillHminusHighContourMomentFamilies q
  let N := max Nt (max Nb Na)
  have hN : 2 ≤ N := hNt.trans (le_max_left _ _)
  have hNt' : Nt ≤ N := le_max_left _ _
  have hNb' : Nb ≤ N := (le_max_left Nb Na).trans (le_max_right _ _)
  have hNa' : Na ≤ N := (le_max_right Nb Na).trans (le_max_right _ _)
  let S : Finset ℕ+ := (Finset.range N).image (fun k : ℕ => (⟨k+1,by omega⟩ : ℕ+))
  obtain ⟨Vh,hVh,hqh,Ah,Rh,hhead⟩ := exists_hillHminus_finite_canonical_period_extensions q hr S
  let W := (Vt ∩ (Vb ∩ Va)) ∩ Vh
  let A : ℕ+ → ℕ → PeriodOneHminusOne → ℂ := fun n m p =>
    if N ≤ (n : ℕ) then hillHminusHighContourMoment (n : ℕ) m p else Ah n m p
  let R : ℕ+ → PeriodOneHminusOne → ℂ := fun n p =>
    if N ≤ (n : ℕ) then hillHminusHighCubicContourMoment (n : ℕ) p else Rh n p
  have hnS (n : ℕ+) (hn : ¬ N ≤ (n : ℕ)) : n ∈ S := by
    have hnpos := n.property
    apply Finset.mem_image.mpr
    refine ⟨(n : ℕ)-1,Finset.mem_range.mpr (by omega),?_⟩
    apply PNat.coe_injective
    change (n : ℕ)-1+1 = (n : ℕ)
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt n.property)
  have hcanon (p : PeriodOneHminusOne) (hp : p ∈ W) (hpr : IsRealPeriodOneHminusOne p) (n : ℕ+) :
      (∀ m, A n m p = hillHminusRealGapContourMoment p hpr n m) ∧
        R n p = hillHminusRealGapCubicContourMoment p hpr n := by
    by_cases hn : N ≤ (n : ℕ)
    · have h := hmatch n (hNt'.trans hn) p hp.1.1 hpr
      simpa only [A,R,if_pos hn] using h
    · have h := (hhead n (hnS n hn)).2.2 p hp.2 hpr
      simpa only [A,R,if_neg hn] using h
  refine ⟨C,N,W,hC,hN,(hVt.inter (hVb.inter hVa)).inter hVh,⟨⟨hqt,hqb,hqa⟩,hqh⟩,A,R,?_,?_,?_,?_,?_⟩
  · intro n m
    by_cases hn : N ≤ (n : ℕ)
    · have h := ((hanalytic n (hNa'.trans hn)).1 m).mono (show W ⊆ Va from fun _ hp => hp.1.2.2)
      simpa only [A,if_pos hn] using h
    · have h := ((hhead n (hnS n hn)).1 m).mono (show W ⊆ Vh from inter_subset_right)
      simpa only [A,if_neg hn] using h
  · intro n
    by_cases hn : N ≤ (n : ℕ)
    · have h := ((hanalytic n (hNa'.trans hn)).2).mono (show W ⊆ Va from fun _ hp => hp.1.2.2)
      simpa only [R,if_pos hn] using h
    · have h := ((hhead n (hnS n hn)).2.1).mono (show W ⊆ Vh from inter_subset_right)
      simpa only [R,if_neg hn] using h
  · intro n hn p
    simp [A,R,hn]
  · intro n hn p hp
    simpa only [A,R,if_pos hn] using (hbound n (hNb'.trans hn)).2.2 p hp.1.2.1
  · intro p hp hpr n
    obtain ⟨hAm,hRm⟩ := hcanon p hp hpr n
    refine ⟨hAm,hRm,?_,?_,?_,?_⟩
    · rw [hAm 0]
      simpa only [Nat.mul_zero] using hillHminusRealGapContourMoment_even_nonneg p hpr n 0
    · rw [hRm]
      exact (hillHminusRealGapCubicContourMoment_nonpositive p hpr n).1
    · rw [hRm]
      exact (hillHminusRealGapCubicContourMoment_nonpositive p hpr n).2
    · rw [hRm,hAm 0]
      exact hillHminusRealGapCubicContourMoment_eq_zero_iff_Arnold_zero p hpr n

end NLS.Articles.KdVConvexity
