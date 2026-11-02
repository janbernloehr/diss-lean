import NLS.Articles.KdVConvexity.GlobalExtension

/-! # Global analytic summation with local spectral cutoffs

High-energy estimates only concern a tail. This file proves that a cutoff
may depend on the action neighborhood: finitely many analytic terms require
no quadratic estimate. All patches use the same literal series, including
on overlaps. The actual KdV action descent and tail estimates remain inputs.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.Articles.KdVConvexity

/-- Remove an arbitrary finite initial set without reindexing the tail. -/
def tailTerms (R : ℕ+ → ActionSpace → ℂ) (s : Finset ℕ+) (n : ℕ+)
    (a : ActionSpace) : ℂ := if n ∈ s then 0 else R n a

/-- A quadratic estimate outside a finite set proves absolute convergence
of the complete series, including its unestimated finite terms. -/
theorem summable_norm_of_tail_quadratic_bound
    (R : ℕ+ → ActionSpace → ℂ) (s : Finset ℕ+) (a : ActionSpace) (C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ n ∉ s, ‖R n a‖ ≤ C * ‖a n‖ ^ 2) :
    Summable (fun n => ‖R n a‖) := by
  have ht : Summable (fun n => ‖tailTerms R s n a‖) :=
    (summable_norm_of_quadratic_bound a (fun n => tailTerms R s n a) C (by
      intro n
      by_cases hn : n ∈ s
      · simp only [tailTerms,if_pos hn,norm_zero]
        exact mul_nonneg hC (sq_nonneg _)
      · simpa only [tailTerms,if_neg hn] using hb n hn)).1
  apply ht.congr_cofinite
  filter_upwards [s.finite_toSet.compl_mem_cofinite] with n hn
  simp only [mem_compl_iff,Finset.mem_coe] at hn
  simp only [tailTerms,if_neg hn]

/-- The exact series equals its finite head plus its masked tail. -/
theorem tsum_eq_head_add_tail (R : ℕ+ → ActionSpace → ℂ) (s : Finset ℕ+)
    (a : ActionSpace) (hs : Summable (fun n => R n a)) :
    (∑' n, R n a) = (∑ n ∈ s, R n a) + ∑' n, tailTerms R s n a := by
  classical
  let head : ℕ+ → ℂ := fun n => if n ∈ s then R n a else 0
  have hh : Summable head := summable_of_ne_finset_zero (s := s) (by
    intro n hn
    simp only [head,if_neg hn])
  have ht : Summable (fun n => tailTerms R s n a) := by
    apply hs.congr_cofinite
    filter_upwards [s.finite_toSet.compl_mem_cofinite] with n hn
    simp only [mem_compl_iff,Finset.mem_coe] at hn
    simp only [tailTerms,if_neg hn]
  have he : (fun n => R n a) = fun n => head n + tailTerms R s n a := by
    funext n
    by_cases hn : n ∈ s <;> simp only [head,tailTerms,hn,ite_true,ite_false,add_zero,zero_add]
  calc
    (∑' n, R n a) = (∑' n, (head n + tailTerms R s n a)) := congrArg tsum he
    _ = (∑' n, head n) + (∑' n, tailTerms R s n a) := hh.tsum_add ht
    _ = (∑ n ∈ s, R n a) + ∑' n, tailTerms R s n a := by
      rw [tsum_eq_sum (s := s) (by intro n hn; simp only [head,if_neg hn])]
      congr 1
      exact Finset.sum_congr rfl (fun n hn => if_pos hn)

/-- The local analytic sum requires quadratic control only on a tail. -/
theorem analyticOnNhd_tsum_of_tail_quadratic_bound
    (R : ℕ+ → ActionSpace → ℂ) (T : Set ActionSpace) (hT : IsOpen T)
    (hR : ∀ n, AnalyticOnNhd ℂ (R n) T) (s : Finset ℕ+) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ a ∈ T, ∀ n ∉ s, ‖R n a‖ ≤ C * ‖a n‖ ^ 2) :
    AnalyticOnNhd ℂ (fun a => ∑' n, R n a) T := by
  have ht : ∀ n, AnalyticOnNhd ℂ (tailTerms R s n) T := by
    intro n
    by_cases hn : n ∈ s
    · have he : tailTerms R s n = fun _ => 0 := funext (fun _ => if_pos hn)
      rw [he]
      exact analyticOnNhd_const
    · have he : tailTerms R s n = R n := funext (fun _ => if_neg hn)
      rw [he]
      exact hR n
  have hsum := analyticOnNhd_tsum_of_local_quadratic_bound (tailTerms R s) T hT ht (by
    intro a ha
    refine ⟨T,hT,ha,subset_rfl,C,hC,?_⟩
    intro b hbT n
    by_cases hn : n ∈ s
    · simp only [tailTerms,if_pos hn,norm_zero]
      exact mul_nonneg hC (sq_nonneg _)
    · simpa only [tailTerms,if_neg hn] using hb b hbT n hn)
  intro a ha
  apply ((s.analyticAt_sum (fun n _ => hR n a ha)).add (hsum a ha)).congr
  filter_upwards [hT.mem_nhds ha] with b hbT
  simpa only [Pi.add_apply,Finset.sum_apply] using (tsum_eq_head_add_tail R s b
    (summable_norm_of_tail_quadratic_bound R s b C hC (hb b hbT)).of_norm).symm

/-- Union of all patches with analytic terms and a quadratically bounded
tail; each patch is allowed its own finite exceptional set and constant. -/
def globalTailSeriesDomain (R : ℕ+ → ActionSpace → ℂ) : Set ActionSpace :=
  ⋃₀ {T : Set ActionSpace | IsOpen T ∧ (∀ n, AnalyticOnNhd ℂ (R n) T) ∧
    ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ T, ∀ n ∉ s, ‖R n a‖ ≤ C * ‖a n‖ ^ 2}

theorem isOpen_globalTailSeriesDomain (R : ℕ+ → ActionSpace → ℂ) :
    IsOpen (globalTailSeriesDomain R) :=
  isOpen_sUnion (fun _ hT => hT.1)

/-- On the full union the literal series is analytic and absolutely
convergent. No cutoff, ordering, or gluing choice is part of the function. -/
theorem analytic_summable_globalTailSeriesDomain (R : ℕ+ → ActionSpace → ℂ) :
    AnalyticOnNhd ℂ (fun a => ∑' n, R n a) (globalTailSeriesDomain R) ∧
      ∀ a ∈ globalTailSeriesDomain R, Summable (fun n => ‖R n a‖) := by
  constructor
  · intro a ha
    obtain ⟨T,⟨hT,hR,s,C,hC,hb⟩,haT⟩ := mem_sUnion.mp ha
    exact analyticOnNhd_tsum_of_tail_quadratic_bound R T hT hR s C hC hb a haT
  · intro a ha
    obtain ⟨T,⟨_,_,s,C,hC,hb⟩,haT⟩ := mem_sUnion.mp ha
    exact summable_norm_of_tail_quadratic_bound R s a C hC (hb a haT)

/-- Allowing a finite exceptional set extends the previously constructed
all-index quadratic domain. -/
theorem globalSeriesDomain_subset_globalTailSeriesDomain
    (R : ℕ+ → ActionSpace → ℂ) : globalSeriesDomain R ⊆ globalTailSeriesDomain R := by
  intro a ha
  obtain ⟨T,⟨hT,hR,C,hC,hb⟩,haT⟩ := mem_sUnion.mp ha
  exact mem_sUnion.mpr ⟨T,⟨hT,hR,∅,C,hC,fun b hbT n _ => hb b hbT n⟩,haT⟩

/-- Reality and nonpositivity of every physical moment pass to the full
sum even when the quadratic estimate is only a tail estimate. -/
theorem tsum_real_nonpositive_on_globalTailSeriesDomain
    (R : ℕ+ → ActionSpace → ℂ) {a : ActionSpace} (ha : a ∈ globalTailSeriesDomain R)
    (hsign : ∀ n, (R n a).im = 0 ∧ (R n a).re ≤ 0) :
    (∑' n, R n a).im = 0 ∧ (∑' n, R n a).re ≤ 0 := by
  have hs := ((analytic_summable_globalTailSeriesDomain R).2 a ha).of_norm
  constructor
  · rw [Complex.im_tsum hs]
    simp only [fun n => (hsign n).1,tsum_zero]
  · rw [Complex.re_tsum hs]
    exact tsum_nonpos (fun n => (hsign n).2)

/-- Local tail estimates at every point give one complex open neighborhood
of the entire nonnegative Hilbert cone, including all boundary points. -/
theorem global_analytic_sum_of_local_tail_bounds
    (R : ℕ+ → ActionSpace → ℂ)
    (hlocal : ∀ a ∈ positiveQuadrant, ∃ T : Set ActionSpace, IsOpen T ∧ a ∈ T ∧
      (∀ n, AnalyticOnNhd ℂ (R n) T) ∧ ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧
        ∀ b ∈ T, ∀ n ∉ s, ‖R n b‖ ≤ C * ‖b n‖ ^ 2) :
    IsOpen (globalTailSeriesDomain R) ∧ positiveQuadrant ⊆ globalTailSeriesDomain R ∧
      AnalyticOnNhd ℂ (fun a => ∑' n, R n a) (globalTailSeriesDomain R) ∧
      ∀ a ∈ globalTailSeriesDomain R, Summable (fun n => ‖R n a‖) := by
  refine ⟨isOpen_globalTailSeriesDomain R,?_,analytic_summable_globalTailSeriesDomain R⟩
  intro a ha
  obtain ⟨T,hT,haT,hR,s,C,hC,hb⟩ := hlocal a ha
  exact mem_sUnion.mpr ⟨T,⟨hT,hR,s,C,hC,hb⟩,haT⟩

end NLS.Articles.KdVConvexity
