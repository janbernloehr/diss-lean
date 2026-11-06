import NLS.Articles.KdVConvexity.BaseContourTailSeries
import NLS.Articles.KdVConvexity.GlobalActionMomentDescent

/-! # Actual analytic contour extension near the entire positive ell2 quadrant

The actual local inverse charts and action-fiber identity are constructed
in the proof. No spectral-coordinate realization is an input. Identifying
this contour Hamiltonian with the physical renormalized KdV Hamiltonian,
its frequencies and its Taylor coefficients remains separate work.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

/-- The actual cubic Hill moments extend analytically to ONE complex
weighted-action neighborhood of the ENTIRE nonnegative cone. Their
literal weighted series is analytic on ONE neighborhood of the whole
positive ell2 quadrant, with exact real recovery, signs and zero value.
This construction is unconditional, but does not assert the physical
Hamiltonian identification required to finish main Theorem 1.1. -/
theorem exists_global_analytic_actual_contour_extension :
    ∃ I : PeriodOneHminusOne → BaseActionSpace,
    ∃ U : Set BaseActionSpace, ∃ R : ℕ+ → BaseActionSpace → ℂ,
      (∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
        (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0) ∧
      IsOpen U ∧ WeightedCoeff.nonnegativeLocus baseActionWeight 1 ⊆ U ∧
      (∀ n, AnalyticOnNhd ℂ (R n) U) ∧
      (∀ q (hr : IsRealPeriodOneHminusOne q), q.val 0 = 0 → ∀ n,
        R n (I q) = hillHminusRealGapCubicContourMoment q hr n) ∧
      (∀ b ∈ U, ∃ T : Set BaseActionSpace, IsOpen T ∧ b ∈ T ∧ T ⊆ U ∧
        ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ T, ∀ n ∉ s,
          ‖weightedContourTerm R n c‖ ≤ C*‖c.val (actionIndexEquiv.symm n)‖^2) ∧
      (∀ b ∈ WeightedCoeff.nonnegativeLocus baseActionWeight 1, ∀ n,
        (R n b).im = 0 ∧ (R n b).re ≤ 0 ∧ (R n b = 0 ↔ b.val (actionIndexEquiv.symm n) = 0)) ∧
      IsOpen (baseActionInclusion ⁻¹' U) ∧ positiveQuadrant ⊆ baseActionInclusion ⁻¹' U ∧
      AnalyticOnNhd ℂ (contourHamiltonian R) (baseActionInclusion ⁻¹' U) ∧
      (∀ a ∈ baseActionInclusion ⁻¹' U,
        Summable (fun n => ‖weightedContourTerm R n (baseActionInclusion a)‖)) ∧
      contourHamiltonian R 0 = 0 ∧
      ∀ a ∈ positiveQuadrant, (contourHamiltonian R a).im = 0 ∧ (contourHamiltonian R a).re ≤ 0 := by
  obtain ⟨Ω,I,_hΩ,hreal,hI,hrec,hpos,_hzero,_hI0,_hinv⟩ :=
    exists_global_analytic_weighted_Arnold_action_map
  obtain ⟨U,R,hU,hcone,hR,hrecover,hbound⟩ := global_cubic_moment_action_descent Ω hreal I hI hrec hpos
  obtain ⟨_W,_hW,_hrealW,A,P,_hA,_hP,hvalues,_hinvariance,_htail⟩ :=
    exists_global_isospectral_canonical_moment_family
  have hsign (b : BaseActionSpace) (hb : b ∈ WeightedCoeff.nonnegativeLocus baseActionWeight 1)
      (n : ℕ+) : (R n b).im = 0 ∧ (R n b).re ≤ 0 ∧
        (R n b = 0 ↔ b.val (actionIndexEquiv.symm n) = 0) := by
    obtain ⟨q,hr,hm,hq⟩ := exists_source_of_nonnegative_Arnold_actions Ω hreal I hI hrec b hb
    have hRp : R n b = P n q := by
      rw [←hq,hrecover q hr hm n,(hvalues q hr n).2.1]
    have hAp : A n 0 q = b.val (actionIndexEquiv.symm n) := by
      rw [(hvalues q hr n).1 0,←hrec q hr n,hq]
    rw [hRp]
    exact ⟨(hvalues q hr n).2.2.2.2.1,(hvalues q hr n).2.2.2.1,
      by simpa only [hAp] using (hvalues q hr n).2.2.2.2.2⟩
  obtain ⟨hopen,hpositive,hH,hsum⟩ :=
    global_analytic_contour_sum_from_base_tail_bounds R U hU hcone hR hbound
  refine ⟨I,U,R,hrec,hU,hcone,hR,hrecover,hbound,hsign,hopen,hpositive,hH,hsum,?_,?_⟩
  · have hz (n : ℕ+) : R n 0 = 0 :=
      ((hsign 0 (WeightedCoeff.zero_mem_nonnegativeLocus baseActionWeight 1) n).2.2).mpr rfl
    simp only [contourHamiltonian,map_zero,weightedContourTerm,hz,mul_zero,tsum_zero]
  · intro a ha
    have hs := (hsum a (hpositive ha)).of_norm
    have hb := baseActionInclusion_mem_nonnegative a ha
    constructor
    · rw [contourHamiltonian,Complex.im_tsum hs]
      have hz (n : ℕ+) : (weightedContourTerm R n (baseActionInclusion a)).im = 0 := by
        simp only [weightedContourTerm,mul_im,ofReal_re,ofReal_im,zero_mul,add_zero,
          (hsign _ hb n).1,mul_zero]
      simp only [hz,tsum_zero]
    · rw [contourHamiltonian,Complex.re_tsum hs]
      apply tsum_nonpos
      intro n
      simp only [weightedContourTerm,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hsign _ hb n).2.1

end NLS.Articles.KdVConvexity
