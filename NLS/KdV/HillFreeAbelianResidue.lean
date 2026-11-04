import NLS.KdV.HillAbelianComplexPeriods
import NLS.KdV.HillFreeAbelianPeriodJacobian

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeAbelianReference_ne_zero_on_disc (k : ℕ) (hk : 1 ≤ k) (z : ℂ)
    (hz : z ∈ closedBall (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k + hillRealGapCollar 0 hq hr k)) :
    hillAbelianPsiCandidate hillFreeGapRoot k z ≠ 0 := by
  intro he
  obtain ⟨j,hjk,hjz⟩ := (hillAbelianPsiCandidate_zero_iff 0 hq hr hillFreeGapRoot
    (hillFreeGapRoot_mem_box hq hr) k hk z).mp he
  have hnot := hillFreeEnergy_notMem_other_gap_disc hq hr (j+1) k (by omega) hk hjk
  apply hnot
  simpa only [hillFreeGapRoot,← hjz] using hz

theorem hillFreeAbelianHilbertPeriod_residue (n k : ℕ) (hk : 1 ≤ k) (a : Coeff 2) :
    hillAbelianHilbertPeriod 0 hq hr n k a =
      hillAbelianHilbertPsi n ((freeHillValue k : ℂ),a) /
        hillAbelianPsiCandidate hillFreeGapRoot k (freeHillValue k : ℂ) := by
  let c := (hillRealGapCenter 0 hq hr k : ℂ)
  let R := hillRealGapHalfLength 0 hq hr k + hillRealGapCollar 0 hq hr k
  let A : ℂ → ℂ := fun z => hillAbelianHilbertPsi n (z,a) /
    hillAbelianPsiCandidate hillFreeGapRoot k z * (Complex.sqrt z)⁻¹
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 hq hr k hk).1
    (hillRealGapContour_geometry 0 hq hr k hk).2.1
  have ha : AnalyticOnNhd ℂ A (closedBall c R) := by
    intro z hz
    have hn : AnalyticAt ℂ (fun w : ℂ => hillAbelianHilbertPsi n (w,a)) z :=
      (analyticOnNhd_hillAbelianHilbertPsi n (z,a) (mem_univ _)).comp (f := fun w : ℂ => (w,a))
        (analyticAt_id.prod analyticAt_const)
    exact (hn.div (analyticOnNhd_hillAbelianPsiCandidate 0 hq hr hillFreeGapRoot
      (hillFreeGapRoot_mem_box hq hr) k z (mem_univ _))
        (hillFreeAbelianReference_ne_zero_on_disc hq hr k hk z hz)).mul
      (analyticOnNhd_hillFreeReciprocalSqrt_on_gap_disc hq hr k hk z hz)
  have he : EqOn (fun z => hillAbelianHilbertPsi n (z,a)/hillEnergyCanonicalRootProduct 0 hq hr z)
      (fun z => (-I*((k : ℂ)*Real.pi))*((z-(freeHillValue k : ℂ))⁻¹ • A z)) (sphere c R) := by
    intro z hz
    have hcut := hillRealGapContour_sphere_subset 0 hq hr k hk hz
    have hp := hillFreeAbelianReference_ne_zero_on_disc hq hr k hk z (sphere_subset_closedBall hz)
    have hd := hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain 0 hq hr z hcut
    have hs : hillAbelianHilbertPsi n (z,a)/hillEnergyCanonicalRootProduct 0 hq hr z =
        (hillAbelianHilbertPsi n (z,a)/hillAbelianPsiCandidate hillFreeGapRoot k z)*
          (hillAbelianPsiCandidate hillFreeGapRoot k z/hillEnergyCanonicalRootProduct 0 hq hr z) := by
      field_simp
    dsimp only []
    rw [hs,hillFreeAbelianQuotient hq hr k hk z hcut]
    dsimp only [A]
    simp only [smul_eq_mul,div_eq_mul_inv,mul_inv_rev,← neg_sub _ z,inv_neg]
    ring
  have hw : (freeHillValue k : ℂ) ∈ ball c R := by
    dsimp only [c]
    rw [hillFreeGapCenter hq hr k hk]
    exact mem_ball_self hR
  have hc := ha.differentiableOn.circleIntegral_sub_inv_smul hw
  unfold hillAbelianHilbertPeriod
  rw [circleIntegral.integral_congr hR.le he,circleIntegral.integral_const_mul,hc]
  dsimp only [A]
  rw [hillFreeGap_sqrt]
  simp only [smul_eq_mul]
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring_nf
  simp only [I_sq]
  ring

end NLS.KdV
