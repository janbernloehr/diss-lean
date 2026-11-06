import NLS.Articles.KdVConvexity.FreeActionRays

/-! # The actual quadratic Hamiltonian coefficient along positive action rays -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.Articles.KdVConvexity
open NLS.KdV

theorem tendsto_weightedContourTerm_div_action_ray_sq
    (I : PeriodOneHminusOne → BaseActionSpace)
    (hI : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (R : ℕ+ → BaseActionSpace → ℂ)
    (hR : ∀ q (hr : IsRealPeriodOneHminusOne q), q.val 0=0 → ∀ n,
      R n (I q)=hillHminusRealGapCubicContourMoment q hr n)
    (v : ActionSpace) (hv : v ∈ positiveQuadrant) (n : ℕ+) :
    Tendsto (fun t : ℝ => weightedContourTerm R n
      (baseActionInclusion (((t^2 : ℝ) : ℂ) • v))/(((t^2 : ℝ) : ℂ)^2))
      (𝓝[≠] 0) (𝓝 (-3*(v n)^2)) := by
  obtain ⟨γ,hγ,hact⟩ := exists_real_rough_action_ray I hI v hv
  obtain ⟨L,hL,hL0,hlocal⟩ := exists_intrinsic_weighted_cubic_action_ratio_at_zero n
  let α : ℝ → ℂ := fun t => ((t^2 : ℝ) : ℂ)
  have hαne : ∀ᶠ t : ℝ in 𝓝[≠] 0, α t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change ((t^2 : ℝ) : ℂ) ≠ 0
    exact_mod_cast pow_ne_zero 2 (show t ≠ 0 from ht)
  have hγval : Tendsto (fun t => (γ t).val) (𝓝 0) (𝓝 (0 : PeriodOneHminusOne)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hγ
  have hlim : Tendsto (fun t : ℝ => (v n)^2*L (γ t).val) (𝓝[≠] 0) (𝓝 (-3*(v n)^2)) := by
    have hh : Tendsto (fun t : ℝ => (v n)^2*L (γ t).val) (𝓝[≠] 0)
        (𝓝 ((v n)^2*L 0)) :=
      tendsto_const_nhds.mul ((hL.continuousAt.tendsto.comp hγval).mono_left nhdsWithin_le_nhds)
    simpa only [hL0,mul_comm] using hh
  apply hlim.congr'
  filter_upwards [hαne,hact.filter_mono nhdsWithin_le_nhds,
    (hγ.eventually hlocal).filter_mono nhdsWithin_le_nhds] with t ht hta htl
  have hraw : hillHminusRealGapContourMoment (γ t).val (γ t).property n 0=α t*v n := by
    have hh := (hI (γ t).val (γ t).property n).symm
    rw [hta.2] at hh
    simpa only [baseActionInclusion_apply,Equiv.apply_symm_apply,lp.coeFn_smul,
      Pi.smul_apply,smul_eq_mul] using hh
  have hr := hR (γ t).val (γ t).property hta.1 n
  rw [hta.2] at hr
  change (v n)^2*L (γ t).val = weightedContourTerm R n (baseActionInclusion (α t • v))/(α t)^2
  rw [weightedContourTerm,hr,htl,hraw]
  field_simp [ht]

theorem positiveQuadrant_real_smul (v : ActionSpace) (hv : v ∈ positiveQuadrant)
    (r : ℝ) (hr : 0 ≤ r) : (r : ℂ) • v ∈ positiveQuadrant := by
  intro n
  constructor
  · change ((r : ℂ)*v n).im=0
    simp only [mul_im,ofReal_re,ofReal_im,(hv n).1,mul_zero,zero_mul,add_zero]
  · change 0 ≤ ((r : ℂ)*v n).re
    simpa only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] using mul_nonneg hr (hv n).2

/-- The literal contour sum has the physical coefficient -3 on every
positive finite-support Hilbert direction. No termwise differentiation
or uniform index-dependent source radius is used. -/
theorem tendsto_contourHamiltonian_div_finite_action_ray_sq
    (I : PeriodOneHminusOne → BaseActionSpace)
    (hI : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (R : ℕ+ → BaseActionSpace → ℂ)
    (hR : ∀ q (hr : IsRealPeriodOneHminusOne q), q.val 0=0 → ∀ n,
      R n (I q)=hillHminusRealGapCubicContourMoment q hr n)
    (hzero : ∀ a ∈ positiveQuadrant, ∀ n : ℕ+, a n=0 → R n (baseActionInclusion a)=0)
    (v : ActionSpace) (hv : v ∈ positiveQuadrant) (S : Finset ℕ+)
    (hs : ∀ n ∉ S, v n=0) :
    Tendsto (fun t : ℝ => contourHamiltonian R (((t^2 : ℝ) : ℂ) • v)/(((t^2 : ℝ) : ℂ)^2))
      (𝓝[≠] 0) (𝓝 (-3*∑ n ∈ S, (v n)^2)) := by
  classical
  have he (t : ℝ) : contourHamiltonian R (((t^2 : ℝ) : ℂ) • v)/(((t^2 : ℝ) : ℂ)^2) =
      ∑ n ∈ S, weightedContourTerm R n (baseActionInclusion (((t^2 : ℝ) : ℂ) • v))/(((t^2 : ℝ) : ℂ)^2) := by
    rw [contourHamiltonian,tsum_eq_sum (s := S),Finset.sum_div]
    intro n hn
    have hz := hzero (((t^2 : ℝ) : ℂ) • v) (positiveQuadrant_real_smul v hv _ (sq_nonneg t)) n
      (by simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,hs n hn,mul_zero])
    simp only [weightedContourTerm,hz,mul_zero]
  have hlim := tendsto_finsetSum S (fun n _ => tendsto_weightedContourTerm_div_action_ray_sq I hI R hR v hv n)
  simpa only [←he,←Finset.mul_sum] using hlim

end NLS.Articles.KdVConvexity
