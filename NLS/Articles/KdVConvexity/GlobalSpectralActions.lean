import NLS.Articles.KdVConvexity.SpectralActionSequence
import NLS.KdV.HillHminusOneCanonicalFreeLabels

/-! # One global analytic weighted Arnold-action map near real H^-1

All actual canonical actions are the raw coordinates of one analytic
map into the weighted ell1 base action space. It preserves realness and
nonnegativity, detects collapsed gaps and is invariant under equality
of the entire real discriminant. No inverse, surjectivity onto the
action cone, or symplectic coordinate identity is inferred.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

theorem exists_global_analytic_weighted_Arnold_action_map :
    ∃ Ω : Set PeriodOneHminusOne, ∃ I : PeriodOneHminusOne → BaseActionSpace,
      IsOpen Ω ∧ {q | IsRealPeriodOneHminusOne q} ⊆ Ω ∧ AnalyticOnNhd ℂ I Ω ∧
      (∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
        (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0) ∧
      (∀ q, IsRealPeriodOneHminusOne q → I q ∈ WeightedCoeff.nonnegativeLocus baseActionWeight 1) ∧
      (∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
        (I q).val (actionIndexEquiv.symm n) = 0 ↔
          hillHminusRealLabels q hr (2*(n : ℕ)-1) = hillHminusRealLabels q hr (2*(n : ℕ))) ∧
      I 0 = 0 ∧ ∀ q p, IsRealPeriodOneHminusOne q → IsRealPeriodOneHminusOne p →
        hillHminusDiscriminant q = hillHminusDiscriminant p → I q = I p := by
  classical
  obtain ⟨W,hW,hrealW,A,P,hA,_,hvalues,hinv,htail⟩ := exists_global_isospectral_canonical_moment_family
  let a : ℕ+ → PeriodOneHminusOne → ℂ := fun n => A n 0
  have hlocal (q : PeriodOneRealHminusOne) :
      ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q.val ∈ V ∧ V ⊆ W ∧
        AnalyticOnNhd ℂ (potentialActionSequence a) V ∧
        ∀ p ∈ V, ∀ k, (potentialActionSequence a p).val k = a (actionIndexEquiv k) p := by
    obtain ⟨_,N,T,_,_,hT,hqT,hTW,hh⟩ := htail q.val q.property
    obtain ⟨V,hV,hqV,hVT,hI,hrec⟩ := exists_analytic_potentialActionSequence_of_high_agreement
      q.val T hT hqT a (fun n => (hA n 0).mono hTW) N (by
        intro n hn p hp
        exact (hh n hn p hp).1 0)
    exact ⟨V,hV,hqV,hVT.trans hTW,hI,hrec⟩
  choose V hV hqV _ hIV hrecV using hlocal
  let Ω : Set PeriodOneHminusOne := ⋃ q : PeriodOneRealHminusOne, V q
  let I := potentialActionSequence a
  have hrealΩ (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) : q ∈ Ω :=
    mem_iUnion.mpr ⟨⟨q,hr⟩,hqV ⟨q,hr⟩⟩
  have hrec (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0 := by
    rw [hrecV ⟨q,hr⟩ q (hqV ⟨q,hr⟩) (actionIndexEquiv.symm n),Equiv.apply_symm_apply]
    exact (hvalues q hr n).1 0
  have hr0 : IsRealPeriodOneHminusOne 0 := by intro k; simp
  refine ⟨Ω,I,isOpen_iUnion hV,hrealΩ,?_,hrec,?_,?_,?_,?_⟩
  · intro p hp
    obtain ⟨q,hpq⟩ := mem_iUnion.mp hp
    exact hIV q p hpq
  · intro q hr k
    have he := hrec q hr (actionIndexEquiv k)
    simp only [Equiv.symm_apply_apply] at he
    rw [he]
    exact ⟨hillHminusRealGapContourMoment_im_eq_zero q hr _ 0,
      hillHminusRealGapContourMoment_even_nonneg q hr _ 0⟩
  · intro q hr n
    rw [hrec q hr n]
    exact hillHminusRealGapContourMoment_zero_eq_zero_iff_closed q hr n
  · apply Subtype.ext
    funext k
    have he := hrec 0 hr0 (actionIndexEquiv k)
    simp only [Equiv.symm_apply_apply] at he
    rw [he]
    apply hillHminusRealGapContourMoment_eq_zero_of_closed 0 hr0 _ 0
    rw [hillHminusRealLabels_zero,hillHminusRealLabels_zero]
    congr 1
    have hp := (actionIndexEquiv k).property
    omega
  intro q p hq hp hD
  apply Subtype.ext
  funext k
  have hqk := hrec q hq (actionIndexEquiv k)
  have hpk := hrec p hp (actionIndexEquiv k)
  simp only [Equiv.symm_apply_apply] at hqk hpk
  rw [hqk,hpk]
  exact ((hillHminusRealGapContourMoments_eq_of_discriminant_eq q p hq hp hD (actionIndexEquiv k)).1 0)

end NLS.Articles.KdVConvexity
