import NLS.KdV.HillHminusPairUniquenessCompatibility
import NLS.KdV.HillHminusOneMomentCutRoot
import NLS.KdV.ClassicalHillActionUpperBound
import NLS.KdV.HillHminusOneArnoldActionComparison

/-! # The actual Arnold actions are bounded by the squared gap scale

The cutoff and complex H^-1 neighborhood precede every index. The estimate
uses the original source-normalized energy period and includes double roots.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_high_arnold_gap_upper_bounds (q : PeriodOneHminusOne) :
    ∃ r C : ℝ, ∃ N : ℕ, ∃ V : Set (PeriodOneHminusOne),
      0 < r ∧ 0 < C ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ V,
        ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
          ‖hillHminusHighContourMoment (n : ℕ) 0 a‖ ≤ C*‖l-u‖^2/(n : ℕ) := by
  obtain ⟨r,A,Nk,Vk,hr,hrpi,hA,hNk,hVk,hqk,hfamily⟩ := exists_hillHminus_gap_cut_roots q
  let rho : ℝ := Real.pi*r/4
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    have hs : Real.pi^2 < 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
    dsimp only [rho]
    nlinarith [mul_le_mul_of_nonneg_left hrpi Real.pi_pos.le]
  obtain ⟨Nm,Vm,_,hVm,hqm,hcover,hperiod⟩ :=
    exists_hillHminus_high_power_period_radius_independence q rho hrho
  refine ⟨r,2*A,max Nk Nm,Vk ∩ Vm,hr,by positivity,hNk.trans_le (le_max_left _ _),
    hVk.inter hVm,⟨hqk,hqm⟩,?_⟩
  intro n hn a ha
  have hnk : Nk ≤ (n : ℕ) := (le_max_left Nk Nm).trans hn
  have hnm : Nm ≤ (n : ℕ) := (le_max_right Nk Nm).trans hn
  obtain ⟨K,_,hmatch,hpairs⟩ := hfamily n hnk
  obtain ⟨l,u,B,hpair,hl,hu,_,hB,hsq,hcollapsed,hbound⟩ := hpairs a ha.1
  let c : ℂ := (freeHillValue (n : ℕ) : ℂ)
  let R : ℝ := Real.pi*(n : ℕ)*r
  have hR : 0 < R := by dsimp only [R]; positivity
  have hcenter : ((Real.pi : ℂ)*(n : ℕ))^2 = c := by
    dsimp only [c,freeHillValue]
    push_cast
    ring
  have hrad : rho*(n : ℝ) = R/4 := by dsimp only [rho,R]; ring
  have hradn : R/4 ≤ (n : ℝ) := by
    rw [← hrad]
    exact mul_le_of_le_one_left (by positivity) hrho1
  have hl' : l ∈ ball c (R/32) := by simpa only [hcenter,R] using hl
  have hu' : u ∈ ball c (R/32) := by simpa only [hcenter,R] using hu
  have hB' : AnalyticOnNhd ℂ B (ball c R \ segment ℝ l u) := by
    simpa only [hcenter,R] using hB
  have hsource (z : ℂ) (hz : z ∈ sphere c (R/4)) : (z,a) ∈ hillHminusContinuationDomain := by
    apply hcover a ha.2 n hnm z
      (closedBall_subset_closedBall hradn (sphere_subset_closedBall hz))
    have he : ‖z-c‖ = R/4 := by simpa only [mem_sphere,dist_eq_norm] using hz
    simpa only [c,hrad,he] using (le_rfl : R/4 ≤ R/4)
  have hraw : -hillHminusHighContourMoment (n : ℕ) 0 a =
      (Real.pi : ℂ)⁻¹*∮ z in C(c,R/4), (hillHminusContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi)^1 := by
    rw [hillHminusHighContourMoment_zero_eq_shifted_period a n (by
      intro z hz
      apply hcover a ha.2 n hnm z (sphere_subset_closedBall hz)
      rw [show ‖z-(freeHillValue (n : ℕ) : ℂ)‖ = (n : ℝ) by
        simpa only [mem_sphere,dist_eq_norm] using hz]
      exact mul_le_of_le_one_left (by positivity) hrho1)]
    simp only [neg_mul,neg_neg]
    simpa only [pow_one,c] using hperiod a ha.2 n hnm (R/4) ⟨hrad.le,hradn⟩ 1
  obtain ⟨k,hk,hM⟩ := hillHminus_power_period_eq_signed_cut_period a n c l u R
    (fun z => K (z,a)) B 1 (-hillHminusHighContourMoment (n : ℕ) 0 a) hR hl' hu' hB'
    (by simpa only [hcenter,R] using hsq)
    (fun z hz hdom => hmatch (z,a) ⟨⟨by
      simpa only [hillHminusGapSquareDisc,classicalHillGapSquareDisc,hcenter,R] using hz,ha.1⟩,hdom⟩)
    hsource hraw
  have hBhalf : AnalyticOnNhd ℂ B (ball c (R/2) \ segment ℝ l u) :=
    hB'.mono (fun z hz => ⟨ball_subset_ball (by linarith : R/2 ≤ R) hz.1,hz.2⟩)
  have hclosedhalf : l = u → AnalyticOnNhd ℂ B (ball c (R/2)) := by
    intro he
    have hh : AnalyticOnNhd ℂ B (ball c R) := by simpa only [hcenter,R] using hcollapsed he
    exact hh.mono (ball_subset_ball (by linarith))
  have hb := norm_primitiveAction_cut_le_gap B c l u (R/2) A (n : ℕ) (by positivity)
    (ball_subset_ball (by linarith : R/32 ≤ (R/2)/8) hl')
    (ball_subset_ball (by linarith : R/32 ≤ (R/2)/8) hu') hBhalf hclosedhalf hbound
  rw [show (R/2)/2 = R/4 by ring] at hb
  have hM' : hillHminusHighContourMoment (n : ℕ) 0 a = k*primitiveAction B c (R/4) := by
    simp only [pow_one] at hM
    unfold primitiveAction
    linear_combination -hM
  refine ⟨l,u,hpair,?_⟩
  rw [hM',norm_mul]
  rcases hk with rfl | rfl <;> simpa using hb


/-- The actual squared gap scale and Arnold action are uniformly comparable
on one complex neighborhood. Both inequalities hold for the same actual pair,
even if the two estimates were constructed with different energy radii. -/
theorem exists_hillHminus_high_arnold_gap_two_sided_bounds (q : PeriodOneHminusOne) :
    ∃ r C : ℝ, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < r ∧ 0 < C ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ V, ∃ l u : ℂ,
        HillHminusHighGapPair a n r l u ∧
        ‖l-u‖^2/(n : ℕ) ≤ 16*Real.pi*‖hillHminusHighContourMoment (n : ℕ) 0 a‖ ∧
        ‖hillHminusHighContourMoment (n : ℕ) 0 a‖ ≤ C*‖l-u‖^2/(n : ℕ) ∧
        (hillHminusHighContourMoment (n : ℕ) 0 a = 0 ↔ l = u) := by
  obtain ⟨r,C,Nu,Vu,hr,hC,hNu,hVu,hqu,hu⟩ :=
    exists_hillHminus_high_arnold_gap_upper_bounds q
  obtain ⟨_,Nl,Vl,_,_,hVl,hql,hl⟩ :=
    exists_hillHminus_high_action_gap_comparison_and_zero_locus q
  refine ⟨r,C,max Nu Nl,Vu ∩ Vl,hr,hC,hNu.trans_le (le_max_left _ _),
    hVu.inter hVl,⟨hqu,hql⟩,?_⟩
  intro n hn a ha
  obtain ⟨l,u,hpair,hupper⟩ := hu n ((le_max_left Nu Nl).trans hn) a ha.1
  obtain ⟨v,w,hpair',hlower,hzero⟩ := hl n ((le_max_right Nu Nl).trans hn) a ha.2
  have hgap : ‖l-u‖ = ‖v-w‖ := by
    rcases hpair.eq_or_swap_between_radii hpair' with he | he
    · rw [he.1,he.2]
    · rw [he.1,he.2,norm_sub_rev]
  have heq : l = u ↔ v = w := by
    simpa only [norm_eq_zero,sub_eq_zero] using
      (show ‖l-u‖ = 0 ↔ ‖v-w‖ = 0 by rw [hgap])
  refine ⟨l,u,hpair,?_,hupper,hzero.trans heq.symm⟩
  rwa [hgap]

end NLS.KdV
