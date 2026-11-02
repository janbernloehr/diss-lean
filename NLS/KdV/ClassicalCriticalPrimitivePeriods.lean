import NLS.KdV.ClassicalNormalizedMomentResolvent
import NLS.KdV.ClassicalCriticalGapLocalization
import NLS.KdV.ClassicalHillWeightedCutPeriods
import NLS.KdV.WeightedCutGapBounds
import NLS.KdV.HighEnergyDiscSeparation

/-! # Actual critical-resolvent primitive periods at gap scale

These are the literal scalar periods in the normalized moment formula.
The cut representation below retains every critical denominator,
including the diagonal pole, on common actual source neighborhoods.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillCriticalPrimitivePeriod (N : ℕ) (j k : ℕ+) (m : ℕ) (q : Curve ℂ) : ℂ :=
  ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
    (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*(2*z)/
      (z^2-classicalHillUniformCriticalPoint N j q)^2

structure ClassicalCriticalPrimitiveCutData (N M : ℕ) (U : Set (Curve ℂ)) (r A : ℝ) : Prop where
  radius_pos : 0 < r
  radius_le : r ≤ Real.pi/4
  bound_pos : 0 < A
  data : ∀ q ∈ U, ∀ k : ℕ+, M ≤ (k : ℕ) → ∃ l u : ℂ, ∃ B : ℂ → ℂ,
    ClassicalHillHighGapPair q k l u ∧
    l ∈ ball (((Real.pi : ℂ)*(k : ℕ))^2) (Real.pi*(k : ℕ)*r/8) ∧
    u ∈ ball (((Real.pi : ℂ)*(k : ℕ))^2) (Real.pi*(k : ℕ)*r/8) ∧
    AnalyticOnNhd ℂ B (ball (((Real.pi : ℂ)*(k : ℕ))^2) (Real.pi*(k : ℕ)*r) \ segment ℝ l u) ∧
    (l = u → AnalyticOnNhd ℂ B (ball (((Real.pi : ℂ)*(k : ℕ))^2) (Real.pi*(k : ℕ)*r))) ∧
    (∀ z ∈ closedBall ((l+u)/2) ‖l-u‖ \ segment ℝ l u, ‖B z‖ ≤ A*‖l-u‖/(k : ℕ)) ∧
    ‖classicalHillUniformCriticalPoint N k q-(l+u)/2‖ ≤ ‖l-u‖/4 ∧
    ∀ j : ℕ+, ∀ m : ℕ, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
      classicalHillCriticalPrimitivePeriod N j k m q = s^m*
        ∮ z in C((((Real.pi : ℂ)*(k : ℕ))^2),Real.pi*(k : ℕ)*r/2),
          B z^m/(z-classicalHillUniformCriticalPoint N j q)^2
  collapsed : ∀ q ∈ U, ∀ k : ℕ+, M ≤ (k : ℕ) → classicalHillHighSquaredGap q k = 0 →
    ∀ j : ℕ+, ∀ m : ℕ, classicalHillCriticalPrimitivePeriod N j k (m+2) q = 0

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem critical_disc_offDiagonal_separation (j k : ℕ+) (hjk : j ≠ k) (q : Curve ℂ) (hq : q ∈ V)
    (z : ℂ) (hz : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
    Real.pi^2/4*|(k : ℝ)^2-(j : ℝ)^2| ≤ ‖z^2-classicalHillUniformCriticalPoint N j q‖ := by
  have hcrit : Complex.sqrt (classicalHillUniformCriticalPoint N j q) ∈
      closedBall ((Real.pi : ℂ)*(j : ℕ)) (Real.pi/4) :=
    mem_closedBall_iff_norm.mpr ((D.critical_close j q hq).le.trans (by linarith [Real.pi_pos]))
  simpa only [sq_sqrt] using highEnergyDiscs_separation j k hjk z _ hz hcrit

theorem critical_energyBall_offDiagonal_separation (j k : ℕ+) (hjk : j ≠ k) (q : Curve ℂ) (hq : q ∈ V)
    (r : ℝ) (hrpi : r ≤ Real.pi/4) (z : ℂ)
    (hz : z ∈ closedBall (((Real.pi : ℂ)*(k : ℕ))^2) (Real.pi*(k : ℕ)*r)) :
    Real.pi^2/4*|(k : ℝ)^2-(j : ℝ)^2| ≤ ‖z-classicalHillUniformCriticalPoint N j q‖ := by
  have hsqrt := sqrt_mem_closedBall_of_energy_disc (Real.pi*(k : ℕ)) r (by positivity) z
    (by simpa only [ofReal_mul,ofReal_natCast] using hz)
  have hsqrt' : Complex.sqrt z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) :=
    closedBall_subset_closedBall hrpi (by simpa only [ofReal_mul,ofReal_natCast] using hsqrt)
  simpa only [sq_sqrt] using D.critical_disc_offDiagonal_separation j k hjk q hq _ hsqrt'

theorem critical_outside_energyBall (j k : ℕ+) (hjk : j ≠ k) (q : Curve ℂ) (hq : q ∈ V)
    (r : ℝ) (hrpi : r ≤ Real.pi/4) :
    classicalHillUniformCriticalPoint N j q ∉ ball (((Real.pi : ℂ)*(k : ℕ))^2) (Real.pi*(k : ℕ)*r) := by
  intro hz
  have hp : 0 < Real.pi^2/4*|(k : ℝ)^2-(j : ℝ)^2| :=
    mul_pos (by positivity) (abs_pos.mpr (positiveIndex_squared_sub_ne_zero k j (Ne.symm hjk)))
  have hh := D.critical_energyBall_offDiagonal_separation j k hjk q hq r hrpi _ (ball_subset_closedBall hz)
  rw [sub_self,norm_zero] at hh
  linarith

theorem identityMoment_eq_critical_primitive (j k : ℕ+) (m : ℕ) (q : Curve ℂ) (hq : q ∈ V) :
    classicalHillNormalizedMoment N (fun _ => ContinuousLinearMap.id ℂ (NLS.Coeff 2)) j k m q =
      (2*(Real.pi : ℂ))/(m+1)*(j : ℂ)*classicalHillCriticalPrimitivePeriod N j k (m+1) q := by
  rw [D.normalizedMoment_eq_resolvent_vector (fun _ => ContinuousLinearMap.id ℂ (NLS.Coeff 2)) j k m q hq]
  simp only [ContinuousLinearMap.id_apply]
  have he : NLS.Coeff.dualPairing (lp.single 2 (j : ℤ) (1 : ℂ)) (classicalHillMomentResolventVector N k m q) =
      classicalHillMomentResolventVector N k m q (j : ℤ) := by
    simp [NLS.Coeff.dualPairing_apply,lp.single_apply,Pi.single_apply]
  rw [he,D.momentResolventVector_positive k j m q hq]
  change (2*(Real.pi : ℂ))/(m+1)*((j : ℂ)*classicalHillCriticalPrimitivePeriod N j k (m+1) q) = _
  ring

theorem exists_critical_primitive_cut_data (q0 : Curve ℂ) (hq0 : q0 ∈ V) :
    ∃ M : ℕ, ∃ U : Set (Curve ℂ), ∃ r C : ℝ,
      0 < M ∧ U ⊆ V ∧ IsOpen U ∧ q0 ∈ U ∧ ClassicalCriticalPrimitiveCutData N M U r C := by
  obtain ⟨r,C,Nb,Vb,hr,hrpi,hC,_,hVb,hqb,hBfamily⟩ := exists_classicalHill_gap_cut_roots q0
  obtain ⟨Nc,Vc,_,hVc,hqc,hcritical⟩ := exists_classicalHill_relative_critical_gap_bound q0 (1/4) (by positivity)
  obtain ⟨Na,Va,_,hVa,hqa,hannulus⟩ := exists_classicalHill_high_annulus_neighborhood q0 (r/4) (by positivity) (by linarith)
  obtain ⟨Mz,Uz,_,hUzV,hUz,hqz,_,hclosed⟩ := D.exists_normalized_high_collapsed_moments
    (fun _ => ContinuousLinearMap.id ℂ (NLS.Coeff 2)) analyticOnNhd_const q0 hq0
  let M := N+1+2+Nb+Nc+Na+Mz
  let U := Vb ∩ (Vc ∩ (Va ∩ Uz))
  have hUV : U ⊆ V := fun _ ha => hUzV ha.2.2.2
  refine ⟨M,U,r,C,by dsimp only [M];omega,hUV,hVb.inter (hVc.inter (hVa.inter hUz)),
    ⟨hqb,hqc,hqa,hqz⟩,{ radius_pos := hr, radius_le := hrpi, bound_pos := hC, data := ?_, collapsed := ?_ }⟩
  · intro q hq k hk
    have hkN : N < (k : ℕ) := by dsimp only [M] at hk;omega
    have hk2 : 2 ≤ (k : ℕ) := by dsimp only [M] at hk;omega
    have hkb : Nb ≤ (k : ℕ) := by dsimp only [M] at hk;omega
    have hkc : Nc ≤ (k : ℕ) := by dsimp only [M] at hk;omega
    have hka : Na ≤ (k : ℕ) := by dsimp only [M] at hk;omega
    have hqV : q ∈ V := hUV hq
    obtain ⟨K,_,hmatch,hpairs⟩ := hBfamily k hkb
    obtain ⟨l,u,B,hpair,hl,hu,_,hB,hsq,hcollapsed,hbound⟩ := hpairs q hq.1
    have hck : ‖classicalHillUniformCriticalPoint N k q-(l+u)/2‖ ≤ ‖l-u‖/4 := by
      obtain ⟨lc,uc,hcpair,hc⟩ := hcritical q hq.2.1 k hkc
      have he : classicalHillUniformCriticalPoint N k q = classicalHillHighCriticalPoint q k :=
        if_neg (Nat.not_le_of_gt hkN)
      rw [he]
      rcases hcpair.eq_or_swap hpair with ⟨heL,heU⟩ | ⟨heL,heU⟩
      · rw [heL,heU] at hc
        linarith
      · rw [heL,heU,add_comm u l,norm_sub_rev u l] at hc
        linarith
    let c : ℝ := Real.pi*(k : ℕ)
    let E : ℂ := ((Real.pi : ℂ)*(k : ℕ))^2
    let R : ℝ := c*r
    let mu := classicalHillUniformCriticalPoint N k q
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
        z-classicalHillUniformCriticalPoint N j q ≠ 0 := by
      by_cases hj : j = k
      · subst j
        exact hdiag_ne z hfar
      · intro he
        exact D.critical_outside_energyBall j k hj q hqV r hrpi (sub_eq_zero.mp he ▸ hz)
    have hfreq_ne (j : ℕ+) (z : ℂ)
        (hz : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4))
        (hfar : r/4 ≤ ‖z-(Real.pi : ℂ)*(k : ℕ)‖) :
        z^2-classicalHillUniformCriticalPoint N j q ≠ 0 := by
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
    refine ⟨l,u,B,hpair,hl,hu,hB,hcollapsed,hbound,hck,?_⟩
    intro j m
    let W (z : ℂ) := (1 : ℂ)/(z-classicalHillUniformCriticalPoint N j q)^2
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
    have hcover := hannulus q hq.2.2.1 k hka
    have hstart : classicalHillCriticalPrimitivePeriod N j k m q =
        ∮ z in C((Real.pi : ℂ)*(k : ℕ),r/4),
          (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*W (z^2)*(2*z) := by
      have he := classicalHill_frequency_weighted_power_radius_independence W k m q (r/4)
        (by positivity) (by linarith) hcover hWfreq
      rw [← he]
      unfold classicalHillCriticalPrimitivePeriod
      apply circleIntegral.integral_congr (by positivity)
      intro z _
      dsimp only [W]
      ring
    obtain ⟨s,hs,hcut⟩ := classicalHill_weighted_power_period_eq_signed_cut_period q k r
      (fun z => K (z,q)) B l u m W hr hrpi hl hu hB hsq
      (fun z hz hsource => hmatch (z,q) ⟨⟨hz,hq.1⟩,hsource⟩)
      (fun z hz => hcover z (closedBall_subset_closedBall (by linarith) (sphere_subset_closedBall hz))
        (mem_sphere_iff_norm.mp hz).ge) hWshell
    refine ⟨s,hs,?_⟩
    rw [hstart]
    simpa only [classicalHillFrequencyPrimitive,W,div_eq_mul_inv,one_mul] using! hcut
  · intro q hq k hk hgap j m
    have hkz : Mz ≤ (k : ℕ) := by dsimp only [M] at hk;omega
    have hz := hclosed q hq.2.2.2 j k hkz hgap m
    have hform := D.identityMoment_eq_critical_primitive j k (m+1) q (hUV hq)
    rw [hz] at hform
    push_cast at hform
    have hm : (m+1 : ℂ)+1 ≠ 0 := by exact_mod_cast (show (m+1 : ℕ)+1 ≠ 0 by omega)
    have hcoef : (2*(Real.pi : ℂ))/((m+1 : ℂ)+1)*(j : ℂ) ≠ 0 :=
      mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) hm)
        (by exact_mod_cast j.ne_zero)
    have he := (mul_eq_zero.mp hform.symm).resolve_left hcoef
    simpa only [Nat.add_assoc] using he

theorem critical_primitive_gap_bounds {M : ℕ} {U : Set (Curve ℂ)} {r C : ℝ}
    (H : ClassicalCriticalPrimitiveCutData N M U r C) (hUV : U ⊆ V)
    (q : Curve ℂ) (hq : q ∈ U) (k : ℕ+) (hk : M ≤ (k : ℕ)) :
    ∃ l u : ℂ, ClassicalHillHighGapPair q k l u ∧
      (∀ m : ℕ, ‖classicalHillCriticalPrimitivePeriod N k k (m+2) q‖ ≤
        8*Real.pi*C^(m+2)*‖l-u‖^(m+1)/(k : ℕ)^(m+2)) ∧
      ∀ j : ℕ+, j ≠ k → ∀ m : ℕ,
        ‖classicalHillCriticalPrimitivePeriod N j k m q‖ ≤
          (32/Real.pi^3)*C^m*‖l-u‖^(m+1)/((k : ℕ)^m*|(k : ℝ)^2-(j : ℝ)^2|^2) := by
  obtain ⟨l,u,B,hpair,hl,hu,hB,hBcollapsed,hBbound,hcritical,hperiods⟩ := H.data q hq k hk
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
    · have hzero : classicalHillHighSquaredGap q k = 0 := by rw [hpair.squaredGap_eq,he,sub_self,zero_pow (by norm_num : 2 ≠ 0)]
      rw [H.collapsed q hq k hk hzero k m,norm_zero,he,sub_self,norm_zero,
        zero_pow (by omega : m+1 ≠ 0),mul_zero,zero_div]
    have hg : 0 < ‖l-u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
    obtain ⟨s,hs,hperiod⟩ := hperiods k (m+2)
    have hnorm : ‖s^(m+2)‖ = 1 := by rcases hs with rfl | rfl <;> simp
    rw [hperiod,norm_mul,hnorm,one_mul]
    exact norm_power_critical_cut_le B E l u (classicalHillUniformCriticalPoint N k q)
      R C (k : ℕ) m hR H.bound_pos.le ht hlc huc hg hcritical hB hBbound
  · intro j hj m
    let b : ℝ := Real.pi^2/4*|(k : ℝ)^2-(j : ℝ)^2|
    have hdelta : 0 < |(k : ℝ)^2-(j : ℝ)^2| :=
      abs_pos.mpr (positiveIndex_squared_sub_ne_zero k j (Ne.symm hj))
    have hb : 0 < b := mul_pos (by positivity) hdelta
    have hsep (z : ℂ) (hz : z ∈ sphere ((l+u)/2) ‖l-u‖) :
        b ≤ ‖z-classicalHillUniformCriticalPoint N j q‖ :=
      D.critical_energyBall_offDiagonal_separation j k hj q (hUV hq) r H.radius_le z
        (ball_subset_closedBall (hball (sphere_subset_closedBall hz)))
    have hbound := norm_power_resolvent_cut_le B E l u (classicalHillUniformCriticalPoint N j q)
      R C (k : ℕ) b m hR H.bound_pos.le ht hb hlc huc hB hBcollapsed
      (D.critical_outside_energyBall j k hj q (hUV hq) r H.radius_le) hBbound hsep
    obtain ⟨s,hs,hperiod⟩ := hperiods j m
    have hnorm : ‖s^m‖ = 1 := by rcases hs with rfl | rfl <;> simp
    rw [hperiod,norm_mul,hnorm,one_mul]
    apply hbound.trans_eq
    dsimp only [b]
    field_simp
    ring

theorem highPeriod_eq_critical_primitive (j k : ℕ+) (q : Curve ℂ) (hq : q ∈ V) :
    classicalHillUniformHighPeriod N j k q = (j : ℂ)*classicalHillCriticalPrimitivePeriod N j k 1 q := by
  simpa only [classicalHillCriticalPrimitivePeriod,pow_one] using!
    classicalHillUniformHighPeriod_eq_primitive N j k q (I*(k : ℂ)*Real.pi)
      (D.numerator_factor j q hq) (D.cover k q hq) (D.critical_sub_ne_zero_on_contour j k q hq)

theorem highPeriod_gap_bound {M : ℕ} {U : Set (Curve ℂ)} {r C : ℝ}
    (H : ClassicalCriticalPrimitiveCutData N M U r C) (hUV : U ⊆ V)
    (q : Curve ℂ) (hq : q ∈ U) (k : ℕ+) (hk : M ≤ (k : ℕ)) :
    ∃ l u : ℂ, ClassicalHillHighGapPair q k l u ∧
      ∀ j : ℕ+, j ≠ k → ‖classicalHillUniformHighPeriod N j k q‖ ≤
        ((32/Real.pi^3)*C)*(j : ℕ)*‖l-u‖^2/((k : ℕ)*|(k : ℝ)^2-(j : ℝ)^2|^2) := by
  obtain ⟨l,u,hpair,_,hbound⟩ := D.critical_primitive_gap_bounds H hUV q hq k hk
  refine ⟨l,u,hpair,?_⟩
  intro j hj
  rw [D.highPeriod_eq_critical_primitive j k q (hUV hq),norm_mul,Complex.norm_natCast]
  have hb := mul_le_mul_of_nonneg_left (hbound j hj 1) (show (0 : ℝ) ≤ (j : ℕ) by positivity)
  apply hb.trans_eq
  simp only [pow_one]
  ring

end ClassicalAllContourPeriodData

/-- Constructed actual bounds on one local source neighborhood, before
all numerator indices, high contour indices and power orders. -/
theorem exists_classicalHill_critical_primitive_gap_bounds :
    ∃ N M : ℕ, ∃ U : Set (Curve ℂ), ∃ C : ℝ,
      0 < N ∧ 0 < M ∧ IsOpen U ∧ 0 ∈ U ∧ 0 < C ∧
        ∀ q ∈ U, ∀ k : ℕ+, M ≤ (k : ℕ) → ∃ l u : ℂ,
          ClassicalHillHighGapPair q k l u ∧
          (∀ m : ℕ, ‖classicalHillCriticalPrimitivePeriod N k k (m+2) q‖ ≤
            8*Real.pi*C^(m+2)*‖l-u‖^(m+1)/(k : ℕ)^(m+2)) ∧
          ∀ j : ℕ+, j ≠ k → ∀ m : ℕ,
            ‖classicalHillCriticalPrimitivePeriod N j k m q‖ ≤
              (32/Real.pi^3)*C^m*‖l-u‖^(m+1)/((k : ℕ)^m*|(k : ℝ)^2-(j : ℝ)^2|^2) := by
  obtain ⟨N,V,A,hN,D⟩ := exists_classicalHill_all_contour_period_data
  obtain ⟨M,U,r,C,hM,hUV,hU,h0U,H⟩ := D.exists_critical_primitive_cut_data 0 D.zero_mem
  exact ⟨N,M,U,C,hN,hM,hU,h0U,H.bound_pos,fun q hq k hk => D.critical_primitive_gap_bounds H hUV q hq k hk⟩

end NLS.KdV
