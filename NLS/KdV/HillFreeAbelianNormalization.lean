import NLS.KdV.HillFreeAbelianQuotient
import NLS.KdV.HillRealGapContourDiscs
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeGapEndpoints (n : ℕ) (hn : 1 ≤ n) :
    hillRealLabels 0 hq hr (2*n-1) = freeHillValue n ∧
      hillRealLabels 0 hq hr (2*n) = freeHillValue n := by
  rw [hillRealLabels_zero,hillRealLabels_zero]
  have hi : (2*n-1+1)/2 = n := by omega
  have hj : (2*n+1)/2 = n := by omega
  rw [hi,hj]
  exact ⟨rfl,rfl⟩

theorem hillFreeGapCenter (n : ℕ) (hn : 1 ≤ n) :
    hillRealGapCenter 0 hq hr n = freeHillValue n := by
  obtain ⟨hl,hu⟩ := hillFreeGapEndpoints hq hr n hn
  rw [hillRealGapCenter,hl,hu]
  ring

theorem hillFreeGap_sqrt (n : ℕ) :
    Complex.sqrt (freeHillValue n : ℂ) = (n : ℂ)*Real.pi := by
  have hval : freeHillValue n = ((n : ℝ)*Real.pi)^2 := by
    simp only [freeHillValue,Int.cast_natCast]
    ring
  have hnonneg : 0 ≤ freeHillValue n := by rw [hval]; positivity
  rw [Complex.sqrt_of_nonneg (by exact_mod_cast hnonneg),ofReal_re,hval,
    Real.sqrt_sq (by positivity : 0 ≤ (n : ℝ)*Real.pi),ofReal_mul,ofReal_natCast]

theorem hillFreeEnergy_notMem_other_gap_disc (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hnk : n ≠ k) :
    (freeHillValue n : ℂ) ∉ closedBall (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k + hillRealGapCollar 0 hq hr k) := by
  intro hz
  have hf := hillRealGapContour_closedBall_subset_filledDomain 0 hq hr k hk hz
  have hs := not_mem_other_gap_of_mem_hillGapFilledDomain 0 hq hr k n hn hnk
    (freeHillValue n : ℂ) hf
  apply hs
  rw [(hillFreeGapEndpoints hq hr n hn).1]
  exact left_mem_segment ℝ _ _

theorem analyticOnNhd_hillFreeReciprocalSqrt_on_gap_disc (k : ℕ) (hk : 1 ≤ k) :
    AnalyticOnNhd ℂ (fun z : ℂ => (Complex.sqrt z)⁻¹)
      (closedBall (hillRealGapCenter 0 hq hr k : ℂ)
        (hillRealGapHalfLength 0 hq hr k + hillRealGapCollar 0 hq hr k)) := by
  intro z hz
  have hs := hillRealGapContour_closedBall_groundShift_slitPlane 0 hq hr k hk z hz
  rw [hillRealLabels_zero_ground hq hr,ofReal_zero,sub_zero] at hs
  have ha := Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hs)
  apply ha.inv
  intro he
  have hsq : (Complex.sqrt z)^2 = z := by
    have h := Complex.cpow_nat_inv_pow z (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  rw [he,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  exact zero_notMem_slitPlane (hsq.symm ▸ hs)

theorem hillFreeAbelianPeriod_Cauchy (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    hillAbelianCandidatePeriod 0 hq hr hillFreeGapRoot n k =
      (2*(Real.pi : ℂ))⁻¹ * (-I*((n : ℂ)*Real.pi)) *
        ∮ z in C((hillRealGapCenter 0 hq hr k : ℂ),
          hillRealGapHalfLength 0 hq hr k + hillRealGapCollar 0 hq hr k),
          (z-(freeHillValue n : ℂ))⁻¹ • (Complex.sqrt z)⁻¹ := by
  obtain ⟨hd,hη,_⟩ := hillRealGapContour_geometry 0 hq hr k hk
  have hR := add_nonneg hd hη.le
  unfold hillAbelianCandidatePeriod
  have he : EqOn
      (fun z => hillAbelianPsiCandidate hillFreeGapRoot n z /
        hillEnergyCanonicalRootProduct 0 hq hr z)
      (fun z => (-I*((n : ℂ)*Real.pi)) *
        ((z-(freeHillValue n : ℂ))⁻¹ • (Complex.sqrt z)⁻¹))
      (sphere (hillRealGapCenter 0 hq hr k : ℂ)
        (hillRealGapHalfLength 0 hq hr k + hillRealGapCollar 0 hq hr k)) := by
    intro z hz
    dsimp only []
    rw [hillFreeAbelianQuotient hq hr n hn z
      (hillRealGapContour_sphere_subset 0 hq hr k hk hz)]
    simp only [smul_eq_mul,div_eq_mul_inv,mul_inv_rev,← neg_sub _ z,inv_neg]
    ring
  rw [circleIntegral.integral_congr hR he,circleIntegral.integral_const_mul]
  ring

theorem hillFreeAbelianPeriod_diagonal (n : ℕ) (hn : 1 ≤ n) :
    hillAbelianCandidatePeriod 0 hq hr hillFreeGapRoot n n = 1 := by
  obtain ⟨hd,hη,_⟩ := hillRealGapContour_geometry 0 hq hr n hn
  have hR : 0 < hillRealGapHalfLength 0 hq hr n + hillRealGapCollar 0 hq hr n :=
    add_pos_of_nonneg_of_pos hd hη
  have hw : (freeHillValue n : ℂ) ∈ ball (hillRealGapCenter 0 hq hr n : ℂ)
      (hillRealGapHalfLength 0 hq hr n + hillRealGapCollar 0 hq hr n) := by
    rw [hillFreeGapCenter hq hr n hn]
    exact mem_ball_self hR
  have hc := (analyticOnNhd_hillFreeReciprocalSqrt_on_gap_disc hq hr n hn).differentiableOn.circleIntegral_sub_inv_smul hw
  rw [hillFreeAbelianPeriod_Cauchy hq hr n n hn hn,hc,hillFreeGap_sqrt]
  simp only [smul_eq_mul]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem hillFreeAbelianPeriod_off_diagonal (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hnk : n ≠ k) :
    hillAbelianCandidatePeriod 0 hq hr hillFreeGapRoot n k = 0 := by
  have hw := hillFreeEnergy_notMem_other_gap_disc hq hr n k hn hk hnk
  have ha : AnalyticOnNhd ℂ (fun z : ℂ =>
      (z-(freeHillValue n : ℂ))⁻¹ • (Complex.sqrt z)⁻¹)
      (closedBall (hillRealGapCenter 0 hq hr k : ℂ)
        (hillRealGapHalfLength 0 hq hr k + hillRealGapCollar 0 hq hr k)) := by
    intro z hz
    have hne : z-(freeHillValue n : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (fun he => hw (he ▸ hz))
    have ha0 : AnalyticAt ℂ (fun w : ℂ => (w-(freeHillValue n : ℂ))⁻¹) z :=
      (analyticAt_id.sub analyticAt_const).inv hne
    exact ha0.smul
      (analyticOnNhd_hillFreeReciprocalSqrt_on_gap_disc hq hr k hk z hz)
  have hc := (DiffContOnCl.mk_ball (ha.differentiableOn.mono ball_subset_closedBall)
    ha.continuousOn).circleIntegral_eq_zero
      (add_nonneg (hillRealGapContour_geometry 0 hq hr k hk).1
        (hillRealGapContour_geometry 0 hq hr k hk).2.1.le)
  rw [hillFreeAbelianPeriod_Cauchy hq hr n k hn hk,hc,mul_zero]

theorem hillFreeAbelianPeriod_eq_delta (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    hillAbelianCandidatePeriod 0 hq hr hillFreeGapRoot n k = if k = n then 1 else 0 := by
  by_cases hkn : k = n
  · subst k
    rw [if_pos rfl]
    exact hillFreeAbelianPeriod_diagonal hq hr n hn
  · rw [if_neg hkn]
    exact hillFreeAbelianPeriod_off_diagonal hq hr n k hn hk (Ne.symm hkn)

theorem hillAbelianNormalizedRoots_zero_nonempty (n : ℕ) (hn : 1 ≤ n) :
    (hillAbelianNormalizedRoots 0 hq hr n).Nonempty := by
  refine ⟨⟨hillFreeGapRoot,hillFreeGapRoot_mem_box hq hr⟩,?_⟩
  intro k hk
  exact hillFreeAbelianPeriod_eq_delta hq hr n k hn hk

end NLS.KdV
