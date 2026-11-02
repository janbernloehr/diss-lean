import NLS.KdV.HillHminusOneGapQuotientAsymptotics
import NLS.KdV.HillHminusOnePairUniqueness
import NLS.KdV.HillHminusOneCubicGapBounds
import NLS.KdV.ClassicalHillActionGapBounds

/-! # Uniform actual H^-1 Arnold-period comparisons and quadratic bounds

The exact free unit normalization controls the actual squared gap by its
source-normalized Arnold period on one complex H^-1 neighborhood. Combined
with the quartic gap bound, it gives the quadratic weighted cubic-moment
estimate in the same topology, including collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_high_action_gap_comparison_and_zero_locus (q : PeriodOneHminusOne) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (PeriodOneHminusOne), 0 < r ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ V, ∃ l u : ℂ,
        HillHminusHighGapPair a n r l u ∧
          ‖l-u‖^2/(n : ℕ) ≤ 16*Real.pi*‖hillHminusHighContourMoment (n : ℕ) 0 a‖ ∧
          (hillHminusHighContourMoment (n : ℕ) 0 a = 0 ↔ l = u) := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_hillHminus_near_free_gap_units q
  obtain ⟨Nk,Vk,hNk,hVk,hqk,hKfamily⟩ := hfamily (1/64) (by norm_num) (by norm_num)
  let rho : ℝ := Real.pi*r/4
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    have hs : Real.pi^2 < 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
    dsimp only [rho]
    nlinarith [mul_le_mul_of_nonneg_left hrpi Real.pi_pos.le]
  obtain ⟨Na,Va,_,hVa,hqa,hcover,hperiod⟩ :=
    exists_hillHminus_high_power_period_radius_independence q rho hrho
  let N := max Nk Na
  let V := Vk ∩ Va
  refine ⟨r,N,V,hr,hNk.trans_le (le_max_left _ _),hVk.inter hVa,⟨hqk,hqa⟩,?_⟩
  intro n hn a ha
  have hnk : Nk ≤ (n : ℕ) := (le_max_left Nk Na).trans hn
  have hna : Na ≤ (n : ℕ) := (le_max_right Nk Na).trans hn
  obtain ⟨K,_,_,hmatch,hpairs⟩ := hKfamily n hnk
  obtain ⟨l,u,H,hpair,hl,hu,hH,hunits⟩ := hpairs a ha.1
  let c : ℝ := Real.pi*(n : ℕ)
  let E : ℂ := (c : ℂ)^2
  let R : ℝ := c*r
  have hc : 0 < c := by dsimp only [c]; positivity
  have hR : 0 < R := mul_pos hc hr
  have hsmall : ((1/64 : ℝ)/64)*R ≤ R/32 := by nlinarith
  have hl' : l ∈ ball E (R/32) := by
    apply ball_subset_ball hsmall
    simpa only [E,R,c,ofReal_mul,ofReal_natCast] using hl
  have hu' : u ∈ ball E (R/32) := by
    apply ball_subset_ball hsmall
    simpa only [E,R,c,ofReal_mul,ofReal_natCast] using hu
  have hH' : AnalyticOnNhd ℂ H (closedBall E R) := by
    simpa only [hillHminusGapSquareDisc,classicalHillGapSquareDisc,E,R,c,ofReal_mul,ofReal_natCast] using hH
  have hunit' (z : ℂ) (hz : z ∈ closedBall E R) :
      H z ≠ 0 ∧ K (z,a) = (z-l)*(z-u)*H z^2 ∧
        ‖H z-I/(2*(c : ℂ))‖ ≤ (1/64)/(2*c) := by
    have hh := hunits z (by simpa only [hillHminusGapSquareDisc,classicalHillGapSquareDisc,E,R,c,ofReal_mul,ofReal_natCast] using hz)
    refine ⟨hh.1,hh.2.2.1,?_⟩
    simpa only [c,ofReal_mul,ofReal_natCast,mul_assoc] using hh.2.2.2
  let B : ℂ → ℂ := fun z => endpointRoot l u z*H z
  have hB : AnalyticOnNhd ℂ B (ball E R \ segment ℝ l u) := by
    intro z hz
    exact (analyticOnNhd_endpointRoot l u z hz.2).mul (hH' z (ball_subset_closedBall hz.1))
  have hBsq (z : ℂ) (hz : z ∈ ball E R \ segment ℝ l u) : B z ≠ 0 ∧ B z^2 = K (z,a) := by
    have hh := hunit' z (ball_subset_closedBall hz.1)
    refine ⟨mul_ne_zero (endpointRoot_ne_zero l u z hz.2) hh.1,?_⟩
    dsimp only [B]
    rw [mul_pow,endpointRoot_sq l u z hz.2,hh.2.1]
  have hcenter : E = (freeHillValue (n : ℕ) : ℂ) := by
    dsimp only [E,c,freeHillValue]
    push_cast
    ring
  have hrad : rho*(n : ℝ) = R/4 := by dsimp only [rho,R,c]; ring
  have hradn : R/4 ≤ (n : ℝ) := by
    rw [← hrad]
    exact mul_le_of_le_one_left (by positivity) hrho1
  have hsource (z : ℂ) (hz : z ∈ sphere E (R/4)) : (z,a) ∈ hillHminusContinuationDomain := by
    have hz' : z ∈ sphere (freeHillValue (n : ℕ) : ℂ) (R/4) := by simpa only [hcenter] using hz
    apply hcover a ha.2 n hna z
      (closedBall_subset_closedBall hradn (sphere_subset_closedBall hz'))
    rw [hrad]
    exact (show ‖z-(freeHillValue (n : ℕ) : ℂ)‖ = R/4 by
      simpa only [mem_sphere,dist_eq_norm] using hz').ge
  have hfull (z : ℂ) (hz : z ∈ sphere (freeHillValue (n : ℕ) : ℂ) (n : ℝ)) :
      (z,a) ∈ hillHminusContinuationDomain := by
    apply hcover a ha.2 n hna z (sphere_subset_closedBall hz)
    have he : ‖z-(freeHillValue (n : ℕ) : ℂ)‖ = (n : ℝ) := by
      simpa only [mem_sphere,dist_eq_norm] using hz
    rw [he]
    exact mul_le_of_le_one_left (by positivity) hrho1
  have hraw : -hillHminusHighContourMoment (n : ℕ) 0 a =
      (Real.pi : ℂ)⁻¹ * ∮ z in C(E,R/4),
        (hillHminusContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi)^1 := by
    rw [hillHminusHighContourMoment_zero_eq_shifted_period a n hfull]
    simp only [neg_mul,neg_neg]
    simpa only [pow_one,hcenter] using hperiod a ha.2 n hna (R/4) ⟨hrad.le,hradn⟩ 1
  obtain ⟨k,hk,heq⟩ := hillHminus_power_period_eq_signed_cut_period a n E l u R
    (fun z => K (z,a)) B 1 (-hillHminusHighContourMoment (n : ℕ) 0 a) hR hl' hu' hB hBsq
    (fun z hz hdom => hmatch (z,a) ⟨⟨by
      simpa only [hillHminusGapSquareDisc,classicalHillGapSquareDisc,E,R,c,ofReal_mul,ofReal_natCast] using hz,ha.1⟩,hdom⟩)
    hsource hraw
  have hA : hillHminusHighContourMoment (n : ℕ) 0 a = k*primitiveAction B E (R/4) := by
    simp only [pow_one] at heq
    unfold primitiveAction
    linear_combination -heq
  have hnormA : ‖hillHminusHighContourMoment (n : ℕ) 0 a‖ = ‖primitiveAction B E (R/4)‖ := by
    rw [hA,norm_mul]
    rcases hk with rfl | rfl <;> simp
  have hcollapsed (he : l = u) : hillHminusHighContourMoment (n : ℕ) 0 a = 0 := by
    subst u
    have hbident : B = fun z => (l-z)*H z := by
      funext z
      simp only [B,endpointRoot,sub_self,zero_pow (by norm_num : 2 ≠ 0),
        NLS.ZakharovShabat.normalizedStandardRoot_zeroGap,show (l+l)/2 = l by ring]
    have hbwhole : AnalyticOnNhd ℂ B (closedBall E R) := by
      rw [hbident]
      exact (analyticOnNhd_const.sub analyticOnNhd_id).mul hH'
    have hz := primitiveAction_eq_zero_of_analyticOnNhd B E (R/4) (by positivity)
      (hbwhole.mono (closedBall_subset_closedBall (by linarith : R/4 ≤ R)))
    rw [hA,hz,mul_zero]
  by_cases hlu : l = u
  · refine ⟨l,u,hpair,?_,⟨fun _ => hlu,fun _ => hcollapsed hlu⟩⟩
    simp only [hlu,sub_self,norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_div]
    positivity
  have hinner := closed_gap_ball_subset_energy_ball l u E R hR
    (show ‖l-E‖ < R/8 by
      have hh : ‖l-E‖ < R/32 := by simpa only [mem_ball,dist_eq_norm] using hl'
      linarith).le
    (show ‖u-E‖ < R/8 by
      have hh : ‖u-E‖ < R/32 := by simpa only [mem_ball,dist_eq_norm] using hu'
      linarith).le
  have hHcircle : ContinuousOn H (sphere ((l+u)/2) ‖l-u‖) := by
    intro z hz
    exact (hH' z (ball_subset_closedBall (hinner (sphere_subset_closedBall hz)))).continuousAt.continuousWithinAt
  have hclose (z : ℂ) (hz : z ∈ sphere ((l+u)/2) ‖l-u‖) :
      ‖H z-I/(2*(c : ℂ))‖ ≤ (1/64)/(2*c) :=
    (hunit' z (ball_subset_closedBall (hinner (sphere_subset_closedBall hz)))).2.2
  have hlower := norm_endpointRoot_unit_action_lower l u H c (1/64) hc (by norm_num) hlu hHcircle hclose
  have hBhalf : AnalyticOnNhd ℂ B (ball E (R/2) \ segment ℝ l u) :=
    hB.mono (fun z hz => ⟨ball_subset_ball (by linarith : R/2 ≤ R) hz.1,hz.2⟩)
  have hdeform := primitiveAction_cut_eq_gap_circle B E l u (R/2) (by positivity)
    (ball_subset_ball (by linarith : R/32 ≤ (R/2)/8) hl')
    (ball_subset_ball (by linarith : R/32 ≤ (R/2)/8) hu') hlu hBhalf
  rw [show (R/2)/2 = R/4 by ring] at hdeform
  change ‖l-u‖^2/(16*c) ≤ ‖primitiveAction B ((l+u)/2) ‖l-u‖‖ at hlower
  rw [← hdeform,← hnormA] at hlower
  have hgap : ‖l-u‖^2/(n : ℕ) ≤ 16*Real.pi*‖hillHminusHighContourMoment (n : ℕ) 0 a‖ := by
    calc
      _ = (16*Real.pi)*(‖l-u‖^2/(16*c)) := by
        have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
        dsimp only [c]
        field_simp [Real.pi_ne_zero,hnpos.ne']
      _ ≤ (16*Real.pi)*‖hillHminusHighContourMoment (n : ℕ) 0 a‖ :=
        mul_le_mul_of_nonneg_left hlower (by positivity)
  refine ⟨l,u,hpair,hgap,⟨?_,hcollapsed⟩⟩
  intro hzero
  have hpos : 0 < ‖l-u‖^2/(n : ℕ) := by
    exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hlu))) (by positivity)
  rw [hzero,norm_zero,mul_zero] at hgap
  linarith

theorem exists_hillHminus_high_action_gap_comparison (q : PeriodOneHminusOne) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (PeriodOneHminusOne), 0 < r ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ V, ∃ l u : ℂ,
        HillHminusHighGapPair a n r l u ∧
          ‖l-u‖^2/(n : ℕ) ≤ 16*Real.pi*‖hillHminusHighContourMoment (n : ℕ) 0 a‖ := by
  obtain ⟨r,N,V,hr,hN,hV,hq,hfamily⟩ := exists_hillHminus_high_action_gap_comparison_and_zero_locus q
  refine ⟨r,N,V,hr,hN,hV,hq,?_⟩
  intro n hn a ha
  obtain ⟨l,u,hpair,hbound,_⟩ := hfamily n hn a ha
  exact ⟨l,u,hpair,hbound⟩

/-- The literal moment and Arnold action are analytic on the same
complex neighborhood, and the exact weighted moment has a quadratic
bound in that action period. All high actual pairs, including collapsed
ones, are covered by one cutoff. This is not action-space descent. -/
theorem exists_analytic_hillHminus_moments_with_action_bounds (q : PeriodOneHminusOne) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ V : Set (PeriodOneHminusOne), 0 < C ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) →
        AnalyticOnNhd ℂ (hillHminusHighCubicContourMoment (n : ℕ)) V ∧
        AnalyticOnNhd ℂ (hillHminusHighContourMoment (n : ℕ) 0) V ∧
        ∀ a ∈ V,
          ‖((8*(n : ℕ)*Real.pi : ℝ) : ℂ)*hillHminusHighCubicContourMoment (n : ℕ) a‖ ≤
            C*‖hillHminusHighContourMoment (n : ℕ) 0 a‖^2 := by
  obtain ⟨_,Cm,Nm,Vm,_,hCm,hNm,hVm,hqm,hmoments⟩ := exists_analytic_hillHminus_moments_with_gap_bounds q
  obtain ⟨_,Ni,Vi,_,_,hVi,hqi,hgap⟩ := exists_hillHminus_high_action_gap_comparison q
  obtain ⟨Na,Va,_,hVa,hqa,haction⟩ := exists_analytic_hillHminusHighContourMomentFamilies q
  let N := max Nm (max Ni Na)
  let V := Vm ∩ (Vi ∩ Va)
  refine ⟨Cm*(16*Real.pi)^2,N,V,by positivity,hNm.trans_le (le_max_left _ _),
    hVm.inter (hVi.inter hVa),⟨hqm,hqi,hqa⟩,?_⟩
  intro n hn
  have hnm : Nm ≤ (n : ℕ) := (le_max_left Nm _).trans hn
  have hni : Ni ≤ (n : ℕ) := (le_max_left Ni Na).trans ((le_max_right Nm _).trans hn)
  have hna : Na ≤ (n : ℕ) := (le_max_right Ni Na).trans ((le_max_right Nm _).trans hn)
  refine ⟨(hmoments n hnm).1.mono (fun _ h => h.1),
    ((haction n hna).1 0).mono (fun _ h => h.2.2),?_⟩
  intro a ha
  obtain ⟨l,u,hpair,hb⟩ := (hmoments n hnm).2 a ha.1
  obtain ⟨li,ui,hpairi,hi⟩ := hgap n hni a ha.2.1
  have hnormgap : ‖l-u‖ = ‖li-ui‖ := by
    rcases hpair.eq_or_swap hpairi with he | he
    · rw [he.1,he.2]
    · rw [he.1,he.2,norm_sub_rev]
  rw [← hnormgap] at hi
  calc
    _ ≤ Cm*(‖l-u‖^2/(n : ℕ))^2 := hb
    _ ≤ Cm*((16*Real.pi)*‖hillHminusHighContourMoment (n : ℕ) 0 a‖)^2 := by gcongr
    _ = (Cm*(16*Real.pi)^2)*‖hillHminusHighContourMoment (n : ℕ) 0 a‖^2 := by ring

end NLS.KdV
