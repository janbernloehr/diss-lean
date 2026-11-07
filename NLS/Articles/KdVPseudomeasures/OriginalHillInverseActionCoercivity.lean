import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapRiccatiBound
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapApproximation
import NLS.KdV.HillRiccatiMeanZeroLift

/-! A universal source norm bound from the actual inverse-frequency action
mass. Finite-gap estimates pass to EVERY rough source in the original norm. -/
noncomputable section
open Set Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem continuous_hillNativeInverseActionMass : Continuous hillNativeInverseActionMass := by
  have he : hillNativeInverseActionMass=(fun q => ‖hillRealSignedMap q‖^2/(2*Real.pi)) :=
    funext hillNativeInverseActionMass_eq_norm_sq
  rw [he]
  have hc : Continuous hillRealSignedMap :=
    continuous_iff_continuousAt.mpr (fun q => (analyticAt_hillRealSignedMap q).continuousAt)
  exact (hc.norm.pow 2).div_const _

theorem norm_hillReal_finiteGap_le_inverseActionMass
    (q : HillRealMeanZeroSource) (hf : q ∈ hillRealFiniteGapLocus) :
    ‖q‖ ≤ hillMiuraNormBoundConstant*
      (Real.sqrt (hillNativeInverseActionMass q)+hillNativeInverseActionMass q) := by
  obtain ⟨u,hu0,hu⟩ := exists_mean_zero_real_Miura_lift q
  have hb := norm_sq_mean_zero_finiteGap_lift_le_inverseActionMass q hf u hu0 (‖u.val‖^2) hu
  have hn : ‖u.val‖ ≤ Real.sqrt (hillNativeInverseActionMass q) :=
    (Real.le_sqrt (norm_nonneg _) (hillNativeInverseActionMass_nonneg q)).mpr hb
  have h := norm_hillRealSource_le_of_shiftedMiura q u (‖u.val‖^2) hu
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add hn hb) hillMiuraNormBoundConstant_pos.le)

/-- Genuine coercivity on the ENTIRE original real Hminus domain. -/
theorem norm_hillReal_le_inverseActionMass (q : HillRealMeanZeroSource) :
    ‖q‖ ≤ hillMiuraNormBoundConstant*
      (Real.sqrt (hillNativeInverseActionMass q)+hillNativeInverseActionMass q) := by
  obtain ⟨g,_,_,ht,hfinite⟩ := hillPhysicalNativeFiniteGap_approximation q
  have hP := continuous_hillNativeInverseActionMass.continuousAt.tendsto.comp ht
  exact le_of_tendsto_of_tendsto ht.norm
    ((Real.continuous_sqrt.continuousAt.tendsto.comp hP).add hP |>.const_mul hillMiuraNormBoundConstant)
    (hfinite.mono fun _ h => norm_hillReal_finiteGap_le_inverseActionMass _ h.1)

end NLS.Articles.KdVPseudomeasures
