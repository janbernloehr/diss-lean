import NLS.Articles.KdVConvexity.FiniteArnoldRealization
import NLS.KdV.HillActionCoefficientLimits
import NLS.KdV.HillMiuraGroundEnergy

/-! # The whole nonnegative weighted Arnold cone has actual rough preimages -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.KdV

/-- Every nonnegative weighted-ell1 action sequence is realized by an
actual real mean-zero Hminus1 Hill potential. The proof constructs finite
physical inverses and passes to a bounded real Miura-factor limit. -/
theorem exists_source_of_nonnegative_Arnold_actions
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q} ⊆ Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (b : BaseActionSpace) (hb : b ∈ WeightedCoeff.nonnegativeLocus baseActionWeight 1) :
    ∃ q : PeriodOneHminusOne, IsRealPeriodOneHminusOne q ∧ q.val 0 = 0 ∧ I q = b := by
  classical
  choose q hr hm hq using exists_source_finite_Arnold_head I hrec b hb
  choose u hu hi hn _ht _hl _hr _ha using
    fun j => exists_periodOneMiura_ground_factor (q j) (hr j) (hm j)
  have he (j : ℕ) : hillNormalizedMiuraSource (u j) = q j := by
    unfold hillNormalizedMiuraSource
    rw [hn j,hi j,add_sub_cancel_right]
  let E : ℝ := (2/Real.pi)*‖b‖
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hbound (j : ℕ) : ‖(u j).val‖^2 ≤ E := by
    rw [hn j]
    apply (ground_energy_le_global_Arnold_norm Ω hΩ I hI hrec (q j) (hr j) (hm j)).trans
    rw [hq j]
    exact mul_le_mul_of_nonneg_left (WeightedCoeff.norm_truncate_le baseActionWeight 1 _ b)
      (by positivity)
  have hbu : Bornology.IsBounded (range (fun j => (u j).val)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨Real.sqrt E,?_⟩
    rintro _ ⟨j,rfl⟩
    have hs := Real.sq_sqrt hE
    have hp := Real.sqrt_nonneg E
    nlinarith [hbound j,norm_nonneg (u j).val]
  have hlim (n : ℕ+) : Tendsto (fun j =>
      hillHminusRealGapContourMoment (hillNormalizedMiuraSource (u j))
        (hillNormalizedMiuraSource_real (u j)) n 0) atTop
      (𝓝 (b.val (actionIndexEquiv.symm n))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n : ℕ)] with j hj
    have hh := hrec (q j) (hr j) n
    rw [hq j,WeightedCoeff.truncate_apply] at hh
    simp only [mem_baseActionHeadSet,if_pos hj] at hh
    simpa only [he j] using hh
  obtain ⟨p,hp,hmp,hap⟩ := exists_hillSource_of_bounded_factor_action_limits u hu hbu
    (fun n => b.val (actionIndexEquiv.symm n)) hlim
  refine ⟨p,hp,hmp,?_⟩
  apply Subtype.ext
  funext k
  have hh := (hrec p hp (actionIndexEquiv k)).trans (hap (actionIndexEquiv k))
  simpa only [Equiv.symm_apply_apply] using hh

/-- Unconditional existence of the actual global analytic weighted Arnold
map, with surjectivity onto the entire nonnegative cone, including its
infinite-dimensional boundary. -/
theorem exists_global_analytic_Arnold_map_onto_cone :
    ∃ Ω : Set PeriodOneHminusOne, ∃ I : PeriodOneHminusOne → BaseActionSpace,
      IsOpen Ω ∧ {q | IsRealPeriodOneHminusOne q} ⊆ Ω ∧ AnalyticOnNhd ℂ I Ω ∧
      (∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
        (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0) ∧
      (∀ q, IsRealPeriodOneHminusOne q → I q ∈ WeightedCoeff.nonnegativeLocus baseActionWeight 1) ∧
      ∀ b ∈ WeightedCoeff.nonnegativeLocus baseActionWeight 1,
        ∃ q : PeriodOneHminusOne, IsRealPeriodOneHminusOne q ∧ q.val 0 = 0 ∧ I q = b := by
  obtain ⟨Ω,I,hΩ,hreal,hI,hrec,hpos,_hzero,_hI0,_hinv⟩ :=
    exists_global_analytic_weighted_Arnold_action_map
  exact ⟨Ω,I,hΩ,hreal,hI,hrec,hpos,
    exists_source_of_nonnegative_Arnold_actions Ω hreal I hI hrec⟩

/-- In particular every point of the positive ell2 quadrant, with no size,
strict-positivity or finite-support condition, has an actual source. -/
theorem exists_source_of_positive_ell2_actions (a : ActionSpace) (ha : a ∈ positiveQuadrant) :
    ∃ q : PeriodOneHminusOne, ∃ hr : IsRealPeriodOneHminusOne q,
      q.val 0 = 0 ∧ ∀ n : ℕ+, hillHminusRealGapContourMoment q hr n 0 = a n := by
  obtain ⟨Ω,I,_hΩ,hreal,hI,hrec,_hpos⟩ := exists_global_analytic_Arnold_map_with_coercivity
  obtain ⟨q,hr,hm,hq⟩ := exists_source_of_nonnegative_Arnold_actions Ω hreal I hI hrec
    (baseActionInclusion a) (baseActionInclusion_mem_nonnegative a ha)
  refine ⟨q,hr,hm,?_⟩
  intro n
  rw [←hrec q hr n,hq,baseActionInclusion_apply,Equiv.apply_symm_apply]

end NLS.Articles.KdVConvexity
