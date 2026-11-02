import NLS.KdV.HillHminusOneRealGapSquares
import NLS.KdV.HillHminusOneArnoldActionComparison
import NLS.ComplexAnalysis.PhysicalCutCubicGeometry

/-! # Nonpositivity of the actual high H^-1 cubic periods

The filled square is nonnegative along the actual real gap. Physical
half-plane signs determine both boundary values; the counterclockwise
jump and exact source-circle deformation fix the sign of the original
period, with its literal factor 1/pi and shift i*n*pi.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_high_cubic_period_nonpositive (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ V, IsRealPeriodOneHminusOne a →
        (hillHminusHighCubicContourMoment (n : ℕ) a).re ≤ 0 ∧
          (hillHminusHighCubicContourMoment (n : ℕ) a).im = 0 := by
  obtain ⟨r,hr,hrpi,Nk,Vk,hNk,hVk,hqk,hfamily⟩ :=
    exists_hillHminus_nonnegative_high_gap_squares q
  let rho : ℝ := Real.pi*r/4
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    have hs : Real.pi^2 < 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
    dsimp only [rho]
    nlinarith [mul_le_mul_of_nonneg_left hrpi Real.pi_pos.le]
  obtain ⟨Nm,Vm,_,hVm,hqm,hcover,hperiod⟩ :=
    exists_hillHminus_high_power_period_radius_independence q rho hrho
  refine ⟨max Nk Nm,Vk ∩ Vm,hNk.trans_le (le_max_left _ _),hVk.inter hVm,⟨hqk,hqm⟩,?_⟩
  intro n hn a ha hreal
  have hnk : Nk ≤ (n : ℕ) := (le_max_left Nk Nm).trans hn
  have hnm : Nm ≤ (n : ℕ) := (le_max_right Nk Nm).trans hn
  obtain ⟨K,hK,hmatch,hpairs⟩ := hfamily n hnk
  obtain ⟨l,u,B,hlu,_,hl,hu,hB,hsq,hgap⟩ := hpairs a ha.1 hreal
  let c : ℝ := freeHillValue (n : ℕ)
  let R : ℝ := Real.pi*(n : ℕ)*r
  have hR : 0 < R := by dsimp only [R]; positivity
  have hcenter : ((Real.pi : ℂ)*(n : ℕ))^2 = (c : ℂ) := by
    dsimp only [c,freeHillValue]; push_cast; ring
  have hrad : rho*(n : ℝ) = R/4 := by dsimp only [rho,R]; ring
  have hradn : R/4 ≤ (n : ℝ) := by
    rw [← hrad]
    exact mul_le_of_le_one_left (by positivity) hrho1
  have hl' : (l : ℂ) ∈ ball (c : ℂ) (R/32) := by simpa only [hcenter,R] using hl
  have hu' : (u : ℂ) ∈ ball (c : ℂ) (R/32) := by simpa only [hcenter,R] using hu
  have hB' : AnalyticOnNhd ℂ B (ball (c : ℂ) R \ segment ℝ (l : ℂ) (u : ℂ)) := by
    simpa only [hcenter,R] using hB
  have hsq' : ∀ z ∈ ball (c : ℂ) R \ segment ℝ (l : ℂ) (u : ℂ),
      B z ≠ 0 ∧ B z^2 = K (z,a) := by simpa only [hcenter,R] using hsq
  have hmatch' (z : ℂ) (hz : z ∈ closedBall (c : ℂ) R)
      (hd : (z,a) ∈ hillHminusContinuationDomain) :
      K (z,a) = (hillHminusContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi)^2 :=
    hmatch (z,a) ⟨⟨by
      simpa only [hillHminusGapSquareDisc,classicalHillGapSquareDisc,hcenter,R] using hz,ha.1⟩,hd⟩
  have hsource (z : ℂ) (hz : z ∈ sphere (c : ℂ) (R/4)) : (z,a) ∈ hillHminusContinuationDomain := by
    apply hcover a ha.2 n hnm z
      (closedBall_subset_closedBall hradn (sphere_subset_closedBall hz))
    have he : ‖z-(c : ℂ)‖ = R/4 := by simpa only [mem_sphere,dist_eq_norm] using hz
    simpa only [c,hrad,he] using (le_rfl : R/4 ≤ R/4)
  obtain ⟨k,hk,hcircle,hupper,hlower⟩ := exists_hillHminus_physical_cut_sign a hreal n c
    l u R (fun z => K (z,a)) B hR hl' hu' hB' hsq' hmatch' hsource
  have hk2 : k^2 = 1 := by rcases hk with rfl | rfl <;> norm_num
  have hsign := circleIntegral_cubic_re_nonpos_of_real_endpoints
    (fun z => k*B z) (fun z => K (z,a)) c l u R hR hlu hl' hu'
    (analyticOnNhd_const.mul hB')
    (by
      intro z hz
      exact (hK (z,a) ⟨by
        simpa only [hillHminusGapSquareDisc,classicalHillGapSquareDisc,hcenter,R] using
          ball_subset_closedBall hz,ha.1⟩).comp
        (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const))
    (fun z hz => by rw [mul_pow,hk2,one_mul,(hsq' z hz).2])
    (fun x hx => (hgap x hx).1) (fun x hx => (hgap x hx).2) hupper hlower
  have hraw : hillHminusHighCubicContourMoment (n : ℕ) a =
      (Real.pi : ℂ)⁻¹*∮ z in C((c : ℂ),R/4), (k*B z)^3 := by
    have hp := hperiod a ha.2 n hnm (R/4) ⟨hrad.le,hradn⟩ 3
    change hillHminusHighCubicContourMoment (n : ℕ) a =
      (Real.pi : ℂ)⁻¹*∮ z in C((c : ℂ),R/4),
        (hillHminusContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi)^3 at hp
    rw [hp]
    congr 1
    apply circleIntegral.integral_congr (by positivity)
    intro z hz
    exact congrArg (fun w : ℂ => w^3) (hcircle z hz).symm
  rw [hraw]
  constructor
  · simpa only [← ofReal_inv,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] using
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr Real.pi_pos.le) hsign.1
  · simp only [← ofReal_inv,mul_im,ofReal_re,ofReal_im,hsign.2,mul_zero,zero_mul,add_zero]

/-- The actual high cubic and Arnold periods remain analytic and obey
the quadratic weighted-action estimate on the same complex neighborhood
on which real cubic periods are nonpositive. -/
theorem exists_analytic_nonpositive_hillHminus_moments_with_action_bounds
    (q : PeriodOneHminusOne) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < C ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) →
        AnalyticOnNhd ℂ (hillHminusHighCubicContourMoment (n : ℕ)) V ∧
        AnalyticOnNhd ℂ (hillHminusHighContourMoment (n : ℕ) 0) V ∧
        (∀ a ∈ V,
          ‖((8*(n : ℕ)*Real.pi : ℝ) : ℂ)*hillHminusHighCubicContourMoment (n : ℕ) a‖ ≤
            C*‖hillHminusHighContourMoment (n : ℕ) 0 a‖^2) ∧
        ∀ a ∈ V, IsRealPeriodOneHminusOne a →
          (hillHminusHighCubicContourMoment (n : ℕ) a).re ≤ 0 ∧
            (hillHminusHighCubicContourMoment (n : ℕ) a).im = 0 := by
  obtain ⟨C,Nb,Vb,hC,hNb,hVb,hqb,hbounds⟩ := exists_analytic_hillHminus_moments_with_action_bounds q
  obtain ⟨Ns,Vs,_,hVs,hqs,hsign⟩ := exists_hillHminus_high_cubic_period_nonpositive q
  refine ⟨C,max Nb Ns,Vb ∩ Vs,hC,hNb.trans_le (le_max_left _ _),hVb.inter hVs,⟨hqb,hqs⟩,?_⟩
  intro n hn
  have hnb : Nb ≤ (n : ℕ) := (le_max_left Nb Ns).trans hn
  have hns : Ns ≤ (n : ℕ) := (le_max_right Nb Ns).trans hn
  exact ⟨((hbounds n hnb).1).mono inter_subset_left,
    ((hbounds n hnb).2.1).mono inter_subset_left,
    fun a ha => (hbounds n hnb).2.2 a ha.1,
    fun a ha hreal => hsign n hns a ha.2 hreal⟩

end NLS.KdV
