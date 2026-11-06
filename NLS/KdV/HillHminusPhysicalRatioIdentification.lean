import NLS.KdV.HillPhysicalGapOpening
import NLS.KdV.HillActionGapRatioAllBase
import NLS.KdV.HillHminusOriginalSourceAdapter

/-! # Physical actions determine continuous rough ratios at every base

Cancellation is used only at open gaps. The proved density of those gaps
and continuity identify the ratio at a collapsed gap as well.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

theorem hillHminus_action_ratio_eq_of_physical_action_germ_at
    (p : RealPeriodOneHillPotential) (n : ℕ+) (R : PeriodOneHminusOne → ℂ)
    (hR : ContinuousAt R (hillOriginalHminusSource p.val))
    (haction : ∀ᶠ v : RealPeriodOneHillPotential in 𝓝 p,
      (hillRealGapIntegral v.val v.property.1 v.property.2 (n : ℕ) 0 : ℂ) =
        (hillRealGapHalfLength v.val v.property.1 v.property.2 (n : ℕ) : ℂ)^2*
          R (hillOriginalHminusSource v.val)) :
    R (hillOriginalHminusSource p.val) =
      hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ) := by
  have hf : ∃ᶠ v : RealPeriodOneHillPotential in 𝓝 p,
      R (hillOriginalHminusSource v.val) =
        hillActionGapRatio v.val v.property.1 v.property.2 (n : ℕ) := by
    apply ((frequently_hillRealGapHalfLength_ne_zero_at p n).and_eventually haction).mono
    intro v hv
    apply mul_left_cancel₀ (pow_ne_zero 2 (ofReal_ne_zero.mpr hv.1))
    exact hv.2.symm.trans
      (hillRealGapIntegral_eq_halfLength_sq_mul_ratio v.val v.property.1 v.property.2
        (n : ℕ) n.property)
  exact tendsto_nhds_unique_of_frequently_eq
    (hR.comp (f := fun v : RealPeriodOneHillPotential => hillOriginalHminusSource v.val)
      (hillOriginalHminusSource.continuous.comp continuous_subtype_val).continuousAt).tendsto
    (continuous_hillActionGapRatio (n : ℕ) n.property).continuousAt.tendsto hf

end NLS.KdV
