import NLS.KdV.HillHminusOneNormalizedMomentKernel
import NLS.KdV.HillHminusOneWeightedCutPeriods
import NLS.KdV.WeightedCutGapBounds
import NLS.KdV.HighEnergyDiscSeparation

/-! # Actual rough critical primitive periods and cut representations

One rough neighborhood retains the actual selected critical poles, the same
endpoint pair and cut root, and all signed power-period identities.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

def hillHminusCriticalPrimitivePeriod (C : HillHminusMiuraChart) (N : ℕ)
    (j k : ℕ+) (m : ℕ) (q : PeriodOneHminusOne) : ℂ :=
  ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
    (hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*(2*z)/
      (z^2-hillHminusUniformCriticalPoint C N j q)^2

structure HillHminusCriticalPrimitiveCutData (C : HillHminusMiuraChart) (N M : ℕ)
    (U : Set PeriodOneHminusOne) (r A : ℝ) : Prop where
  radius_pos : 0 < r
  radius_le : r ≤ Real.pi/4
  bound_pos : 0 < A
  data : ∀ q ∈ U, ∀ k : ℕ+, M ≤ (k : ℕ) → ∃ l u : ℂ, ∃ B : ℂ → ℂ,
    HillHminusHighGapPair q k r l u ∧
    l ∈ ball (((Real.pi : ℂ)*(k : ℕ))^2) (Real.pi*(k : ℕ)*r/8) ∧
    u ∈ ball (((Real.pi : ℂ)*(k : ℕ))^2) (Real.pi*(k : ℕ)*r/8) ∧
    AnalyticOnNhd ℂ B (ball (((Real.pi : ℂ)*(k : ℕ))^2) (Real.pi*(k : ℕ)*r) \ segment ℝ l u) ∧
    (l = u → AnalyticOnNhd ℂ B (ball (((Real.pi : ℂ)*(k : ℕ))^2) (Real.pi*(k : ℕ)*r))) ∧
    (l = u → B l = 0) ∧
    (∀ z ∈ closedBall ((l+u)/2) ‖l-u‖ \ segment ℝ l u, ‖B z‖ ≤ A*‖l-u‖/(k : ℕ)) ∧
    ‖hillHminusUniformCriticalPoint C N k q-(l+u)/2‖ ≤ ‖l-u‖/4 ∧
    (l = u → hillHminusUniformCriticalPoint C N k q = l) ∧
    ∀ j : ℕ+, ∀ m : ℕ, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
      hillHminusCriticalPrimitivePeriod C N j k m q = s^m*
        ∮ z in C((((Real.pi : ℂ)*(k : ℕ))^2),Real.pi*(k : ℕ)*r/2),
          B z^m/(z-hillHminusUniformCriticalPoint C N j q)^2

namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem critical_disc_offDiagonal_separation (j k : ℕ+) (hjk : j ≠ k) (q : PeriodOneHminusOne) (hq : q ∈ V)
    (z : ℂ) (hz : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
    Real.pi^2/4*|(k : ℝ)^2-(j : ℝ)^2| ≤ ‖z^2-hillHminusUniformCriticalPoint C N j q‖ := by
  have hcrit : Complex.sqrt (hillHminusUniformCriticalPoint C N j q) ∈
      closedBall ((Real.pi : ℂ)*(j : ℕ)) (Real.pi/4) :=
    mem_closedBall_iff_norm.mpr ((D.critical_close j q hq).le.trans (by linarith [Real.pi_pos]))
  simpa only [sq_sqrt] using highEnergyDiscs_separation j k hjk z _ hz hcrit

theorem critical_energyBall_offDiagonal_separation (j k : ℕ+) (hjk : j ≠ k) (q : PeriodOneHminusOne) (hq : q ∈ V)
    (r : ℝ) (hrpi : r ≤ Real.pi/4) (z : ℂ)
    (hz : z ∈ closedBall (((Real.pi : ℂ)*(k : ℕ))^2) (Real.pi*(k : ℕ)*r)) :
    Real.pi^2/4*|(k : ℝ)^2-(j : ℝ)^2| ≤ ‖z-hillHminusUniformCriticalPoint C N j q‖ := by
  have hsqrt := sqrt_mem_closedBall_of_energy_disc (Real.pi*(k : ℕ)) r (by positivity) z
    (by simpa only [ofReal_mul,ofReal_natCast] using hz)
  have hsqrt' : Complex.sqrt z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) :=
    closedBall_subset_closedBall hrpi (by simpa only [ofReal_mul,ofReal_natCast] using hsqrt)
  simpa only [sq_sqrt] using D.critical_disc_offDiagonal_separation j k hjk q hq _ hsqrt'

theorem critical_outside_energyBall (j k : ℕ+) (hjk : j ≠ k) (q : PeriodOneHminusOne) (hq : q ∈ V)
    (r : ℝ) (hrpi : r ≤ Real.pi/4) :
    hillHminusUniformCriticalPoint C N j q ∉ ball (((Real.pi : ℂ)*(k : ℕ))^2) (Real.pi*(k : ℕ)*r) := by
  intro hz
  have hp : 0 < Real.pi^2/4*|(k : ℝ)^2-(j : ℝ)^2| :=
    mul_pos (by positivity) (abs_pos.mpr (positiveIndex_squared_sub_ne_zero k j (Ne.symm hjk)))
  have hh := D.critical_energyBall_offDiagonal_separation j k hjk q hq r hrpi _ (ball_subset_closedBall hz)
  rw [sub_self,norm_zero] at hh
  linarith

theorem exists_critical_primitive_cut_data :
    ∃ M : ℕ, ∃ U : Set PeriodOneHminusOne, ∃ r B : ℝ,
      0 < M ∧ U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧ HillHminusCriticalPrimitiveCutData C N M U r B := by
  obtain ⟨r,Mr,Vr,hr,hrpi,_,hVrV,hVr,h0Vr,hBfamily⟩ := D.exists_critical_gap_cut_roots
  obtain ⟨Na,Va,_,hVa,h0Va,hannulus⟩ :=
    exists_hillHminus_high_annulus_neighborhood 0 (r/4) (by positivity)
  let M := Mr+Na+2
  let U := Vr ∩ Va
  have hUV : U ⊆ V := fun _ hq => hVrV hq.1
  refine ⟨M,U,r,3/Real.pi,by dsimp only [M];omega,hUV,hVr.inter hVa,⟨h0Vr,h0Va⟩,
    { radius_pos := hr, radius_le := hrpi, bound_pos := by positivity, data := ?_ }⟩
  intro q hq k hk
  have hk2 : 2 ≤ (k : ℕ) := by dsimp only [M] at hk;omega
  have hkb : Mr ≤ (k : ℕ) := by dsimp only [M] at hk;omega
  have hka : Na ≤ (k : ℕ) := by dsimp only [M] at hk;omega
  have hqV : q ∈ V := hUV hq
  obtain ⟨K,_,hmatch,hpairs⟩ := hBfamily k hkb
  obtain ⟨l,u,B,hpair,hl,hu,_,hB,hsq,hcollapsed,hBzero,hbound',_,hck,hmuCollapsed,_⟩ := hpairs q hq.1
  have hbound : ∀ z ∈ closedBall ((l+u)/2) ‖l-u‖ \ segment ℝ l u,
      ‖B z‖ ≤ (3/Real.pi)*‖l-u‖/(k : ℕ) := by
    intro z hz
    exact (hbound' z hz).trans_eq (by ring)
  let c : ℝ := Real.pi*(k : ℕ)
  let E : ℂ := ((Real.pi : ℂ)*(k : ℕ))^2
  let R : ℝ := c*r
  let mu := hillHminusUniformCriticalPoint C N k q
  have hc : 0 < c := by dsimp only [c];positivity
  have hR : 0 < R := mul_pos hc hr
  have hcC : (c : ℂ) = (Real.pi : ℂ)*(k : ℕ) := by simp only [c,ofReal_mul,ofReal_natCast]
  have hEsq : (c : ℂ)^2 = E := by rw [hcC]
  have hRho : c*(r/4) = R/4 := by dsimp only [R];ring
  have hl' : ‖l-E‖ ≤ R/8 := (mem_ball_iff_norm.mp hl).le
  have hu' : ‖u-E‖ ≤ R/8 := (mem_ball_iff_norm.mp hu).le
  have hmid := norm_complex_midpoint_sub_le l u E (R/8) hl' hu'
  have hgap : ‖l-u‖ ≤ R/4 := by
    have hh := norm_sub_le_norm_sub_add_norm_sub l E u
    rw [norm_sub_rev E u] at hh
    linarith
  have hmuE : ‖mu-E‖ ≤ 3*R/16 := by
    have hh := norm_sub_le_norm_sub_add_norm_sub mu ((l+u)/2) E
    change ‖mu-(l+u)/2‖ ≤ ‖l-u‖/4 at hck
    linarith
  have hdiag_ne (z : ℂ) (hz : R/4 < ‖z-E‖) : z-mu ≠ 0 := by
    intro he
    rw [sub_eq_zero.mp he] at hz
    linarith
  have henergy_ne (j : ℕ+) (z : ℂ) (hz : z ∈ ball E R) (hfar : R/4 < ‖z-E‖) :
      z-hillHminusUniformCriticalPoint C N j q ≠ 0 := by
    by_cases hj : j = k
    · subst j
      exact hdiag_ne z hfar
    · intro he
      exact D.critical_outside_energyBall j k hj q hqV r hrpi (sub_eq_zero.mp he ▸ hz)
  have hfreq_ne (j : ℕ+) (z : ℂ)
      (hz : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4))
      (hfar : r/4 ≤ ‖z-(Real.pi : ℂ)*(k : ℕ)‖) :
      z^2-hillHminusUniformCriticalPoint C N j q ≠ 0 := by
    by_cases hj : j = k
    · subst j
      have hdist : 0 < ‖z-(c : ℂ)‖ := by rw [hcC];linarith
      have hdistpi : ‖z-(c : ℂ)‖ ≤ Real.pi/4 := by rw [hcC];exact mem_closedBall_iff_norm.mp hz
      have hc2 : Real.pi/4 ≤ c/8 := by
        have hkreal : (2 : ℝ) ≤ (k : ℕ) := by exact_mod_cast hk2
        dsimp only [c]
        nlinarith [Real.pi_pos]
      have hsphere : z ∈ sphere (c : ℂ) ‖z-(c : ℂ)‖ := mem_sphere_iff_norm.mpr rfl
      have hh := (norm_sq_sub_sq_of_small_sphere c ‖z-(c : ℂ)‖ hc hdist (hdistpi.trans hc2) z hsphere).1
      rw [hEsq] at hh
      apply hdiag_ne (z^2)
      have hscaled := mul_le_mul_of_nonneg_left hfar hc.le
      rw [← hcC,hRho] at hscaled
      linarith
    · have hp : 0 < Real.pi^2/4*|(k : ℝ)^2-(j : ℝ)^2| :=
        mul_pos (by positivity) (abs_pos.mpr (positiveIndex_squared_sub_ne_zero k j (Ne.symm hj)))
      exact norm_pos_iff.mp (hp.trans_le (D.critical_disc_offDiagonal_separation j k hj q hqV z hz))
  refine ⟨l,u,B,hpair,hl,hu,hB,hcollapsed,hBzero,hbound,hck,hmuCollapsed,?_⟩
  intro j m
  let W (z : ℂ) := (1 : ℂ)/(z-hillHminusUniformCriticalPoint C N j q)^2
  have hWfreq : ∀ z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) \
      ball ((Real.pi : ℂ)*(k : ℕ)) (r/4), AnalyticAt ℂ W (z^2) := by
    intro z hz
    have hfar : r/4 ≤ ‖z-(Real.pi : ℂ)*(k : ℕ)‖ := by
      simpa only [mem_ball,dist_eq_norm,not_lt] using hz.2
    exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow 2)
      (pow_ne_zero _ (hfreq_ne j z hz.1 hfar))
  have hWshell : AnalyticOnNhd ℂ W
      (closedBall E (3*c*(r/4)) \ closedBall E (c*(r/4))) := by
    intro z hz
    have hlow : R/4 < ‖z-E‖ := by
      simpa only [mem_closedBall,dist_eq_norm,not_le,hRho] using hz.2
    have hhigh : ‖z-E‖ ≤ 3*R/4 := by
      have hh := mem_closedBall_iff_norm.mp hz.1
      rw [show 3*c*(r/4) = 3*R/4 by dsimp only [R];ring] at hh
      exact hh
    have hzR : z ∈ ball E R := mem_ball_iff_norm.mpr (by linarith)
    exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow 2)
      (pow_ne_zero _ (henergy_ne j z hzR hlow))
  have hcover := hannulus q hq.2 k hka
  have hstart : hillHminusCriticalPrimitivePeriod C N j k m q =
      ∮ z in C((Real.pi : ℂ)*(k : ℕ),r/4),
        (hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*W (z^2)*(2*z) := by
    have he := hillHminus_frequency_weighted_power_radius_independence W k m q (r/4)
      (by positivity) (by linarith) hcover hWfreq
    rw [← he]
    unfold hillHminusCriticalPrimitivePeriod
    apply circleIntegral.integral_congr (by positivity)
    intro z _
    dsimp only [W]
    ring
  obtain ⟨s,hs,hcut⟩ := hillHminus_weighted_power_period_eq_signed_cut_period q k r
    (fun z => K (z,q)) B l u m W hr hrpi hl hu hB hsq
    (fun z hz hsource => hmatch (z,q) ⟨⟨hz,hq.1⟩,hsource⟩)
    (fun z hz => hcover z (closedBall_subset_closedBall (by linarith) (sphere_subset_closedBall hz))
      (mem_sphere_iff_norm.mp hz).ge) hWshell
  refine ⟨s,hs,?_⟩
  rw [hstart]
  simpa only [hillHminusFrequencyPrimitive,W,div_eq_mul_inv,one_mul] using! hcut

theorem critical_primitive_gap_bounds {M : ℕ} {U : Set (PeriodOneHminusOne)} {r B : ℝ}
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U ⊆ V)
    (q : PeriodOneHminusOne) (hq : q ∈ U) (k : ℕ+) (hk : M ≤ (k : ℕ)) :
    ∃ l u : ℂ, HillHminusHighGapPair q k r l u ∧
      (∀ m : ℕ, ‖hillHminusCriticalPrimitivePeriod C N k k (m+2) q‖ ≤
        8*Real.pi*B^(m+2)*‖l-u‖^(m+1)/(k : ℕ)^(m+2)) ∧
      ∀ j : ℕ+, j ≠ k → ∀ m : ℕ,
        ‖hillHminusCriticalPrimitivePeriod C N j k m q‖ ≤
          (32/Real.pi^3)*B^m*‖l-u‖^(m+1)/((k : ℕ)^m*|(k : ℝ)^2-(j : ℝ)^2|^2) := by
  obtain ⟨l,u,F,hpair,hl,hu,hF,hFcollapsed,hFzero,hFbound,hcritical,hmuCollapsed,hperiods⟩ := H.data q hq k hk
  let E : ℂ := ((Real.pi : ℂ)*(k : ℕ))^2
  let R : ℝ := Real.pi*(k : ℕ)*r
  have hR : 0 < R := by dsimp only [R];exact mul_pos (by positivity) H.radius_pos
  have ht : (0 : ℝ) < (k : ℕ) := by positivity
  have hlc : l ∈ closedBall E (R/8) := ball_subset_closedBall hl
  have huc : u ∈ closedBall E (R/8) := ball_subset_closedBall hu
  have hball := closed_gap_ball_subset_energy_ball l u E R hR
    (mem_closedBall_iff_norm.mp hlc) (mem_closedBall_iff_norm.mp huc)
  refine ⟨l,u,hpair,?_,?_⟩
  · intro m
    by_cases he : l = u
    · have hzero := circleIntegral_power_div_sq_eq_zero_of_analytic_zero F l E (R/2)
        (by positivity) (ball_subset_ball (by linarith) hl)
        ((hFcollapsed he).mono (closedBall_subset_ball (by linarith))) (hFzero he) m
      obtain ⟨t,_,hperiod⟩ := hperiods k (m+2)
      rw [hperiod,hmuCollapsed he,hzero,mul_zero,norm_zero,he,sub_self,norm_zero,
        zero_pow (by omega : m+1 ≠ 0),mul_zero,zero_div]
    have hg : 0 < ‖l-u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
    obtain ⟨s,hs,hperiod⟩ := hperiods k (m+2)
    have hnorm : ‖s^(m+2)‖ = 1 := by rcases hs with rfl | rfl <;> simp
    rw [hperiod,norm_mul,hnorm,one_mul]
    exact norm_power_critical_cut_le F E l u (hillHminusUniformCriticalPoint C N k q)
      R B (k : ℕ) m hR H.bound_pos.le ht hlc huc hg hcritical hF hFbound
  · intro j hj m
    let b : ℝ := Real.pi^2/4*|(k : ℝ)^2-(j : ℝ)^2|
    have hdelta : 0 < |(k : ℝ)^2-(j : ℝ)^2| :=
      abs_pos.mpr (positiveIndex_squared_sub_ne_zero k j (Ne.symm hj))
    have hb : 0 < b := mul_pos (by positivity) hdelta
    have hsep (z : ℂ) (hz : z ∈ sphere ((l+u)/2) ‖l-u‖) :
        b ≤ ‖z-hillHminusUniformCriticalPoint C N j q‖ :=
      D.critical_energyBall_offDiagonal_separation j k hj q (hUV hq) r H.radius_le z
        (ball_subset_closedBall (hball (sphere_subset_closedBall hz)))
    have hbound := norm_power_resolvent_cut_le F E l u (hillHminusUniformCriticalPoint C N j q)
      R B (k : ℕ) b m hR H.bound_pos.le ht hb hlc huc hF hFcollapsed
      (D.critical_outside_energyBall j k hj q (hUV hq) r H.radius_le) hFbound hsep
    obtain ⟨s,hs,hperiod⟩ := hperiods j m
    have hnorm : ‖s^m‖ = 1 := by rcases hs with rfl | rfl <;> simp
    rw [hperiod,norm_mul,hnorm,one_mul]
    apply hbound.trans_eq
    dsimp only [b]
    field_simp
    ring

end HillHminusUniformPeriodData
end NLS.KdV
