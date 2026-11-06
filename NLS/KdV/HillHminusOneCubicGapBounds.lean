import NLS.KdV.HillHminusOneMomentCutRoot
import NLS.KdV.ClassicalHillCubicGapBounds

/-! # Uniform quartic gap bounds for the actual H^-1 cubic moments

The source-normalized radius-n energy period is deformed to a circle
inside the actual cut-root disc, then to the gap-length circle. This
gives the fourth power of the gap uniformly in the complex H^-1 topology.
Collapsed gaps use the analytic continuation through the double root.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_high_cubic_gap_bounds (q : PeriodOneHminusOne) :
    ∃ r C : ℝ, ∃ N : ℕ, ∃ V : Set (PeriodOneHminusOne),
      0 < r ∧ 0 < C ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ V,
        ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
          ‖hillHminusHighCubicContourMoment (n : ℕ) a‖ ≤ C*‖l-u‖^4/(n : ℕ)^3 := by
  obtain ⟨r,A,Nk,Vk,hr,hrpi,hA,hNk,hVk,hqk,hfamily⟩ := exists_hillHminus_gap_cut_roots q
  let rho : ℝ := Real.pi*r/4
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    have hs : Real.pi^2 < 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
    dsimp only [rho]
    nlinarith [mul_le_mul_of_nonneg_left hrpi Real.pi_pos.le]
  obtain ⟨Nm,Vm,_,hVm,hqm,hcover,hperiod⟩ :=
    exists_hillHminus_high_power_period_radius_independence q rho hrho
  refine ⟨r,2*A^3,max Nk Nm,Vk ∩ Vm,hr,by positivity,hNk.trans_le (le_max_left _ _),
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
  have hraw : hillHminusHighCubicContourMoment (n : ℕ) a =
      (Real.pi : ℂ)⁻¹*∮ z in C(c,R/4), (hillHminusContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi)^3 := by
    exact hperiod a ha.2 n hnm (R/4) ⟨hrad.le,hradn⟩ 3
  obtain ⟨k,hk,hM⟩ := hillHminus_power_period_eq_signed_cut_period a n c l u R
    (fun z => K (z,a)) B 3 (hillHminusHighCubicContourMoment (n : ℕ) a) hR hl' hu' hB'
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
  have hb := norm_cubicMoment_cut_le_gap B c l u (R/2) A (n : ℕ) (by positivity)
    (ball_subset_ball (by linarith : R/32 ≤ (R/2)/8) hl')
    (ball_subset_ball (by linarith : R/32 ≤ (R/2)/8) hu') hBhalf hclosedhalf hbound
  rw [show (R/2)/2 = R/4 by ring] at hb
  change hillHminusHighCubicContourMoment (n : ℕ) a = k^3*cubicMoment B c (R/4) at hM
  refine ⟨l,u,hpair,?_⟩
  rw [hM,norm_mul,norm_pow]
  rcases hk with rfl | rfl <;> simpa using hb

/-- The exact summand weight from the renormalized Hamiltonian leaves
the square of the gap/action scale. The remaining action comparison is
not assumed to be a property of an arbitrary coordinate map. -/
theorem exists_hillHminus_high_weighted_cubic_gap_bounds (q : PeriodOneHminusOne) :
    ∃ r C : ℝ, ∃ N : ℕ, ∃ V : Set (PeriodOneHminusOne),
      0 < r ∧ 0 < C ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ V,
        ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
          ‖((8*(n : ℕ)*Real.pi : ℝ) : ℂ)*hillHminusHighCubicContourMoment (n : ℕ) a‖ ≤
            C*(‖l-u‖^2/(n : ℕ))^2 := by
  obtain ⟨r,C,N,V,hr,hC,hN,hV,hq,hbound⟩ := exists_hillHminus_high_cubic_gap_bounds q
  refine ⟨r,8*Real.pi*C,N,V,hr,by positivity,hN,hV,hq,?_⟩
  intro n hn a ha
  obtain ⟨l,u,hpair,hb⟩ := hbound n hn a ha
  have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
  refine ⟨l,u,hpair,?_⟩
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (8*(n : ℕ)*Real.pi)*(C*‖l-u‖^4/(n : ℕ)^3) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (8*Real.pi*C)*(‖l-u‖^2/(n : ℕ))^2 := by
      field_simp [hnpos.ne']

/-- The literal moments are analytic and satisfy their weighted gap
estimate on the same complex neighborhood and with one common cutoff. -/
theorem exists_analytic_hillHminus_moments_with_gap_bounds (q : PeriodOneHminusOne) :
    ∃ r C : ℝ, ∃ N : ℕ, ∃ V : Set (PeriodOneHminusOne),
      0 < r ∧ 0 < C ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) →
        AnalyticOnNhd ℂ (hillHminusHighCubicContourMoment (n : ℕ)) V ∧
        ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
          ‖((8*(n : ℕ)*Real.pi : ℝ) : ℂ)*hillHminusHighCubicContourMoment (n : ℕ) a‖ ≤
            C*(‖l-u‖^2/(n : ℕ))^2 := by
  obtain ⟨r,C,Nb,Vb,hr,hC,hNb,hVb,hqb,hbound⟩ := exists_hillHminus_high_weighted_cubic_gap_bounds q
  obtain ⟨Na,Va,_,hVa,hqa,hanalytic⟩ := exists_analytic_hillHminusHighContourMomentFamilies q
  refine ⟨r,C,max Nb (Na+1),Vb ∩ Va,hr,hC,hNb.trans_le (le_max_left _ _),hVb.inter hVa,
    ⟨hqb,hqa⟩,?_⟩
  intro n hn
  have hnb : Nb ≤ (n : ℕ) := (le_max_left Nb (Na+1)).trans hn
  have hna : Na < (n : ℕ) := by have := (le_max_right Nb (Na+1)).trans hn; omega
  exact ⟨((hanalytic n (le_of_lt hna)).2).mono inter_subset_right,fun a ha => hbound n hnb a ha.1⟩

end NLS.KdV
