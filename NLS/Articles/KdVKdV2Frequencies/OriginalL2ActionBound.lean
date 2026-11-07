import NLS.Articles.KdVKdV2Frequencies.OriginalRoughActionGerms
import NLS.KdV.NativeHillPhysicalSource
import NLS.KdV.HillOriginalQuadraticTrace
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeighted
import NLS.Articles.KdVKdV2Frequencies.NativeSourceSobolevCompatibility

/-! The exact quadratic action trace bounds the literal original
leading actions uniformly on EVERY bounded original real L2 set. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem original_l2_action_weight_bound
    (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((0:ℕ):ℝ))) (n : ℕ+) :
    Weight.sobolev 1 (n:ℤ)*‖D.roughActionCoordinate n (nativeHillSource 0 q.val)‖≤‖q‖^2 := by
  let p := nativeHillPhysicalSource 0 q.val q.property.1
  have hp0 : p.val.val 0=0 := by
    have h := nativeHillPhysicalSource_coefficients 0 q.val q.property.1 0
    simpa only [mul_zero,SpectralWeight.toCoeff_apply,q.property.2] using h
  have hpnorm : ‖p.val‖≤‖q‖ := by
    have h := norm_hillPeriodOneUnitPotential_le SpectralWeight.one (nativeHillUnitRealSource 0 q.val q.property.1).val
    change ‖p.val‖≤‖(nativeHillUnitRealSource 0 q.val q.property.1).val‖ at h
    have hn : ‖(nativeHillUnitRealSource 0 q.val q.property.1).val‖=
        ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 0) q.val‖ := hillUnitSourceLift.norm_map _
    rw [hn] at h
    exact h.trans (WeightedCoeff.norm_sobolevToL2_le (by norm_num) q.val)
  have hI (j : ℕ) : 0≤hillRealGapIntegral p.val p.property.1 p.property.2 (j+1) 0 := by
    simpa only [mul_zero] using hillRealGapIntegral_nonneg_even p.val p.property.1 p.property.2
      (j+1) (by omega) 0
  have hsum := hasSum_hillRealGapIntegrals_quadratic_even_l2 p hp0
  have hsingle := hsum.summable.le_tsum ((n:ℕ)-1) (fun j _ => mul_nonneg (by positivity) (hI j))
  rw [hsum.tsum_eq] at hsingle
  have hnpos := n.pos
  have hn : (n:ℕ)-1+1=(n:ℕ) := by omega
  rw [hn] at hsingle
  have hIn : 0≤hillRealGapIntegral p.val p.property.1 p.property.2 n 0 := by
    have h := hI ((n:ℕ)-1)
    rwa [hn] at h
  have hsrc : nativeHillSource 0 q.val=hillOriginalHminusSource p.val := by
    rw [hillOriginalHminusSource_eq_physical]
    exact nativeHillSource_eq_physical 0 q.val q.property.1
  rw [hsrc,D.roughActionCoordinate_physical,Complex.norm_real,Real.norm_of_nonneg hIn]
  have hn1 : (1:ℝ)≤n := by exact_mod_cast n.pos
  have hw : Weight.sobolev 1 (n:ℤ)=1+(n:ℝ) := by
    simp only [Weight.sobolev_apply,Real.rpow_one,Int.cast_natCast,abs_of_pos (by positivity : (0:ℝ)<n)]
  rw [hw]
  have hsq : ‖p.val‖^2≤‖q‖^2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hpnorm
  have hscale := mul_nonneg (show 0≤2*Real.pi-2 by linarith [Real.pi_gt_three])
    (mul_nonneg (show (0:ℝ)≤n by positivity) hIn)
  have hunit := mul_le_mul_of_nonneg_right hn1 hIn
  nlinarith

theorem native_l2_action_weight_bound
    (D : GlobalRoughAbelianForwardData) (a : physicalRealDeletedSubmodule) (n : ℕ+) :
    Weight.sobolev 1 (n:ℤ)*‖D.roughActionCoordinate n
      (GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num) a)‖≤‖a‖^2 := by
  let e := physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((0:ℕ):ℝ)) (Weight.sobolev_neg ((0:ℕ):ℝ))
  have h := original_l2_action_weight_bound D (e a) n
  have hs := realNativeSource_original_l2 (e a)
  change GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num) (e.symm (e a))=_ at hs
  rw [e.symm_apply_apply] at hs
  rw [←hs,e.norm_map] at h
  exact h

end NLS.Articles.KdVKdV2Frequencies
