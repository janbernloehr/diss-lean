import NLS.ComplexAnalysis.EndpointRootContinuity
import NLS.KdV.HillGlobalDifferentialContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem continuous_hillDeflatedEnergyCanonicalRoot_nonreal (k : ℕ) (hk : 1 ≤ k)
    (z : ℂ) (hz : z.im ≠ 0) :
    Continuous (fun p : RealPeriodOneHillPotential =>
      hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k z) := by
  have hR : Continuous (fun p : RealPeriodOneHillPotential =>
      hillEnergyCanonicalRootProduct p.val p.property.1 p.property.2 z) :=
    continuousOn_hillEnergyCanonicalRootProduct_joint.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => Or.inl hz)
  have hE : Continuous (fun p : RealPeriodOneHillPotential => endpointRoot
      (hillRealLabels p.val p.property.1 p.property.2 (2*k-1) : ℂ)
      (hillRealLabels p.val p.property.1 p.property.2 (2*k) : ℂ) z) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact continuousAt_endpointRoot_of_not_mem_segment _ _ _
      ((continuous_ofReal.comp (continuous_hillRealLabels (2*k-1))).continuousAt)
      ((continuous_ofReal.comp (continuous_hillRealLabels (2*k))).continuousAt)
      continuousAt_const (not_mem_real_segment_of_im_ne_zero _ _ z hz)
  have hEn (p : RealPeriodOneHillPotential) : endpointRoot
      (hillRealLabels p.val p.property.1 p.property.2 (2*k-1) : ℂ)
      (hillRealLabels p.val p.property.1 p.property.2 (2*k) : ℂ) z ≠ 0 := by
    intro he
    have hs := endpointRoot_sq
      (hillRealLabels p.val p.property.1 p.property.2 (2*k-1) : ℂ)
      (hillRealLabels p.val p.property.1 p.property.2 (2*k) : ℂ) z
      (not_mem_real_segment_of_im_ne_zero _ _ z hz)
    rw [he,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
    rcases mul_eq_zero.mp hs.symm with hl | hu
    · exact hz (by simpa using congrArg Complex.im (sub_eq_zero.mp hl))
    · exact hz (by simpa using congrArg Complex.im (sub_eq_zero.mp hu))
  apply (hR.div hE hEn).congr
  intro p
  dsimp only [Pi.div_apply]
  rw [hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated p.val p.property.1 p.property.2 k hk z]
  exact mul_div_cancel_left₀ _ (hEn p)

end NLS.KdV
