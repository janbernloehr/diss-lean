import NLS.KdV.HillCriticalFrequencyBridge
import NLS.ZakharovShabat.CentralCriticalRoots
import NLS.ZakharovShabat.UniformCriticalCounts
import NLS.ComplexAnalysis.RealSquareRootCensus

/-! # Exact original central critical multiplicities for opposite square roots of the selected energy critical values. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
theorem analyticOrderAt_deriv_hillL2Discriminant_ne_top
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) :
    analyticOrderAt (deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q))) z ≠ ⊤ := by
  obtain ⟨a,ha⟩ := exists_deriv_hillL2Discriminant_ne_zero q hq hr
  exact analyticOrderAt_ne_top_on_connected isPreconnected_univ
    (analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q)).deriv (mem_univ a) ha (mem_univ z)

theorem analyticOrderNatAt_canonicalDiscriminant_hill_nonzero (q : Coeff 2) (z : ℂ) (hz : z ≠ 0) :
    analyticOrderNatAt (deriv (canonicalDiscriminant (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential q))) z =
      analyticOrderNatAt (deriv (hillL2Discriminant q)) (z^2) := by
  let f := deriv (hillL2Discriminant q)
  have hpow : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
    convert! (hasDerivAt_id z).pow 2 using 1
    simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,id_eq]
  have hn : (2 : ℂ)*z ≠ 0 := mul_ne_zero (by norm_num) hz
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := f) (g := fun w : ℂ => w^2) (analyticAt_id.pow 2) (by rw [hpow.deriv]; exact hn)
  change analyticOrderAt (fun w : ℂ => f (w^2)) z = analyticOrderAt f (z^2) at hcomp
  have ha := ((analyticOnNhd_hillL2Discriminant q).deriv (z^2) (mem_univ _)).comp
    (f := fun w : ℂ => w^2) (analyticAt_id.pow 2)
  have hmul := analyticOrderAt_mul (analyticAt_const.mul analyticAt_id : AnalyticAt ℂ (fun w : ℂ => 2*w) z) ha
  change analyticOrderAt (fun w : ℂ => 2*w*f (w^2)) z =
    analyticOrderAt (fun w : ℂ => 2*w) z+analyticOrderAt (fun w : ℂ => f (w^2)) z at hmul
  rw [analyticOrderAt_eq_zero.mpr (Or.inr hn),zero_add,hcomp] at hmul
  have hfun : deriv (canonicalDiscriminant (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential q)) =
      (fun w : ℂ => 2*w*f (w^2)) := funext (deriv_canonicalDiscriminant_hillL2CoefficientPotential q)
  rw [hfun]
  exact congrArg ENat.toNat hmul

theorem hillGapCriticalPoint_occurrence_sum_le_one
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range N, if hillGapCriticalPoint q hq hr (k+1) = x then (1 : ℕ) else 0) ≤ 1 := by
  classical
  rw [Finset.sum_boole]
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  exact (hillGapCriticalPoint_strictMono_positive q hq hr).injective (hi'.trans hj'.symm)

theorem hillGapCriticalPoint_occurrence_sum_le_order
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range N, if hillGapCriticalPoint q hq hr (k+1) = x then (1 : ℕ) else 0) ≤
      analyticOrderNatAt (deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q))) (x : ℂ) := by
  classical
  by_cases hs : (∑ k ∈ Finset.range N, if hillGapCriticalPoint q hq hr (k+1) = x then (1 : ℕ) else 0) = 0
  · rw [hs]; exact Nat.zero_le _
  have hp := Nat.pos_of_ne_zero hs
  obtain ⟨k,_,hk⟩ := Finset.sum_pos_iff.mp hp
  have he : hillGapCriticalPoint q hq hr (k+1) = x := by
    by_contra he
    simp only [if_neg he] at hk
    omega
  have hcrit := (hillGapCriticalPoint_spec q hq hr (k+1) (by omega)).2
  rw [he] at hcrit
  apply (hillGapCriticalPoint_occurrence_sum_le_one q hq hr N x).trans
  exact analyticOrderNatAt_pos_of_zero
    ((analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q)).deriv x (mem_univ _))
    (analyticOrderAt_deriv_hillL2Discriminant_ne_top q hq hr x) hcrit

theorem hillGapCriticalPoint_sqrt_mem_centralCircle
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 16*‖q‖ ≤ (N : ℝ)) (k : ℕ) (hk : k < N) :
    Complex.sqrt (hillGapCriticalPoint q hq hr (k+1)) ∈ ball 0 (centralCircleRadius N) := by
  let x := hillGapCriticalPoint q hq hr (k+1)
  have hgap := (hillGapCriticalPoint_spec q hq hr (k+1) (by omega)).1
  have hground := (hillLowestEnergy_mem_centralInterval q hq hr N hN (by linarith [norm_nonneg q])).1
  change -(N : ℝ)^2 < hillRealLabels q hq hr 0 at hground
  have hlo : -(N : ℝ)^2 < x := hground.trans_le
    ((monotone_hillRealLabels q hq hr (Nat.zero_le _)).trans hgap.1)
  obtain ⟨p,_,hu⟩ := hillRealLabels_high_pair q hq hr N hN hcut
  have hp := (abs_le.mp (p.localization q hq N (by omega) (by linarith [norm_nonneg q])).2).2
  have htop : hillRealLabels q hq hr (2*N) ≤ Real.pi^2*(N : ℝ)^2+4*‖q‖ := by
    rw [hu]
    simpa only [freeHillValue,Int.cast_natCast] using (show p.right ≤ freeHillValue N+4*‖q‖ by linarith)
  have hxup : x ≤ Real.pi^2*(N : ℝ)^2+4*‖q‖ :=
    hgap.2.trans ((monotone_hillRealLabels q hq hr (by omega)).trans htop)
  have hcross : (N : ℝ) ≤ Real.pi^2*N := by
    have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ Real.pi^2 by nlinarith [Real.pi_gt_three])
      (Nat.cast_nonneg (α := ℝ) N)
    simpa only [one_mul] using h
  have hup : x < (centralCircleRadius N)^2 := by
    unfold centralCircleRadius
    nlinarith [Real.pi_gt_three]
  have hNR : (N : ℝ) < centralCircleRadius N := by
    unfold centralCircleRadius
    nlinarith [Real.pi_gt_three,Nat.cast_nonneg (α := ℝ) N]
  have habs : |x| < (centralCircleRadius N)^2 := abs_lt.mpr ⟨by nlinarith [Nat.cast_nonneg (α := ℝ) N],hup⟩
  have hs : (Complex.sqrt (x : ℂ))^2 = (x : ℂ) := by
    have h := Complex.cpow_nat_inv_pow (x : ℂ) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hnorm : ‖Complex.sqrt (x : ℂ)‖^2 = |x| := by
    rw [← norm_pow,hs,norm_real,Real.norm_eq_abs]
  rw [mem_ball,dist_zero_right]
  exact (sq_lt_sq₀ (norm_nonneg _) (centralCircleRadius_pos N).le).mp (hnorm.trans_lt habs)

def hillCentralGapCriticalRoots
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) : Multiset ℂ :=
  {0} + ∑ k ∈ Finset.range N,
    {Complex.sqrt (hillGapCriticalPoint q hq hr (k+1)), -Complex.sqrt (hillGapCriticalPoint q hq hr (k+1))}

theorem count_hillCentralGapCriticalRoots_of_sq_real
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (z : ℂ) (x : ℝ)
    (hx : z^2 = (x : ℂ)) :
    (hillCentralGapCriticalRoots q hq hr N).count z = (if z = 0 then 1 else 0)+
      (if z = 0 then 2 else 1)*(∑ k ∈ Finset.range N,
        if hillGapCriticalPoint q hq hr (k+1) = x then (1 : ℕ) else 0) := by
  classical
  rw [hillCentralGapCriticalRoots,Multiset.count_add,Multiset.count_sum']
  simp_rw [count_opposite_square_root_pair]
  have he (k : ℕ) : (Complex.sqrt (hillGapCriticalPoint q hq hr (k+1)))^2 = z^2 ↔ hillGapCriticalPoint q hq hr (k+1) = x := by
    have hs : (Complex.sqrt (hillGapCriticalPoint q hq hr (k+1)))^2 = (hillGapCriticalPoint q hq hr (k+1) : ℂ) := by
      have h := Complex.cpow_nat_inv_pow (hillGapCriticalPoint q hq hr (k+1) : ℂ) (Nat.succ_ne_zero 1)
      norm_num at h
      simpa only [Complex.sqrt,one_div] using h
    rw [hs,hx,Complex.ofReal_inj]
  simp_rw [he]
  rw [Finset.mul_sum]
  simp only [Multiset.count_singleton]


theorem hillCentralGapCriticalRoots_mem_centralCircle
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 16*‖q‖ ≤ (N : ℝ)) (z : ℂ)
    (hz : z ∈ hillCentralGapCriticalRoots q hq hr N) : z ∈ closedBall 0 (centralCircleRadius N) := by
  simp only [hillCentralGapCriticalRoots,Multiset.mem_add,Multiset.mem_singleton,Multiset.mem_sum,
    Multiset.insert_eq_cons,Multiset.mem_cons] at hz
  rcases hz with rfl | ⟨k,hk,hz | hz⟩
  · exact mem_closedBall_self (centralCircleRadius_pos N).le
  · rw [hz]
    exact ball_subset_closedBall (hillGapCriticalPoint_sqrt_mem_centralCircle q hq hr N hN hcut k
      (Finset.mem_range.mp hk))
  · rw [hz]
    have h := ball_subset_closedBall (hillGapCriticalPoint_sqrt_mem_centralCircle q hq hr N hN hcut k
      (Finset.mem_range.mp hk))
    simpa only [mem_closedBall,dist_zero_right,norm_neg] using h

theorem hillCentralGapCriticalRoots_le_original
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 16*‖q‖ ≤ (N : ℝ)) :
    hillCentralGapCriticalRoots q hq hr N ≤ centralCriticalRoots
      (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2 : ℝ≥0∞))
      (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) (hillL2CoefficientPotential_even _) N := by
  classical
  apply Multiset.le_iff_count.mpr
  intro z
  by_cases hc : (hillCentralGapCriticalRoots q hq hr N).count z = 0
  · rw [hc]; exact Nat.zero_le _
  have hm := Multiset.count_pos.mp (Nat.pos_of_ne_zero hc)
  have hcentral := hillCentralGapCriticalRoots_mem_centralCircle q hq hr N hN hcut z hm
  have hreal : ∃ x : ℝ, z^2 = (x : ℂ) := by
    simp only [hillCentralGapCriticalRoots,Multiset.mem_add,Multiset.mem_singleton,Multiset.mem_sum,
      Multiset.insert_eq_cons,Multiset.mem_cons] at hm
    rcases hm with rfl | ⟨k,_,hz | hz⟩
    · exact ⟨0,by simp⟩
    all_goals
      refine ⟨hillGapCriticalPoint q hq hr (k+1),?_⟩
      have hs : (Complex.sqrt (hillGapCriticalPoint q hq hr (k+1)))^2 = (hillGapCriticalPoint q hq hr (k+1) : ℂ) := by
        have h := Complex.cpow_nat_inv_pow (hillGapCriticalPoint q hq hr (k+1) : ℂ) (Nat.succ_ne_zero 1)
        norm_num at h
        simpa only [Complex.sqrt,one_div] using h
      simpa only [hz,neg_sq] using hs
  obtain ⟨x,hx⟩ := hreal
  rw [count_centralCriticalRoots,if_pos hcentral,count_hillCentralGapCriticalRoots_of_sq_real q hq hr N z x hx]
  by_cases hz : z = 0
  · subst z
    have hx0 : x = 0 := by
      have h := congrArg Complex.re hx
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_re,ofReal_re] using h.symm
    subst x
    simp only [if_true,analyticOrderNatAt_canonicalDiscriminant_hill_zero q hq hr]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 (hillGapCriticalPoint_occurrence_sum_le_order q hq hr N 0)) 1
  · simp only [if_neg hz,zero_add,one_mul]
    rw [analyticOrderNatAt_canonicalDiscriminant_hill_nonzero _ z hz,hx]
    exact hillGapCriticalPoint_occurrence_sum_le_order q hq hr N x

theorem hillCentralGapCriticalRoots_eq_original
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 16*‖q‖ ≤ (N : ℝ))
    (hcount : analyticZeroCount (deriv (canonicalDiscriminant (by simp : (2 : ℝ≥0∞) ≠ ⊤)
      (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)))) (closedBall 0 (centralCircleRadius N)) = 2*N+1) :
    hillCentralGapCriticalRoots q hq hr N = centralCriticalRoots
      (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2 : ℝ≥0∞))
      (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) (hillL2CoefficientPotential_even _) N := by
  apply Multiset.eq_of_le_of_card_le (hillCentralGapCriticalRoots_le_original q hq hr N hN hcut)
  rw [card_centralCriticalRoots,hcount]
  simp [hillCentralGapCriticalRoots,Multiset.card_sum,mul_comm]


theorem exists_hillCentralGapCriticalRoots_eq_original
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    ∃ N : ℕ, 2 ≤ N ∧ 16*‖q‖ ≤ (N : ℝ) ∧ ∀ M : ℕ, N ≤ M →
      hillCentralGapCriticalRoots q hq hr M = centralCriticalRoots
        (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2 : ℝ≥0∞))
        (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) (hillL2CoefficientPotential_even _) M := by
  let φ := hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)
  obtain ⟨N0,_,U,_,_,hφ,_,hdata⟩ := exists_uniform_discriminant_critical_distribution
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2 : ℝ≥0∞)) φ
    (r := Real.pi/4) (by positivity) le_rfl
  obtain ⟨_,hcount,_⟩ := hdata φ hφ (hillL2CoefficientPotential_even _)
  let N := max N0 (hillRealLabelCutoff q)
  have hN : 2 ≤ N := (hillRealLabelCutoff_ge_two q).trans (le_max_right _ _)
  have hcut : 16*‖q‖ ≤ (N : ℝ) := (hillRealLabelCutoff_bound q).trans
    (by exact_mod_cast (le_max_right N0 (hillRealLabelCutoff q)))
  refine ⟨N,hN,hcut,?_⟩
  intro M hM
  exact hillCentralGapCriticalRoots_eq_original q hq hr M (hN.trans hM)
    (hcut.trans (by exact_mod_cast hM)) (hcount M ((le_max_left _ _).trans hM)).1



end NLS.KdV
