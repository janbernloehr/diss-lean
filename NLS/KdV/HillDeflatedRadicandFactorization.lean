import NLS.KdV.HillDeflatedCanonicalRoot
import NLS.KdV.HillAbelianComplexRoot
import NLS.ComplexAnalysis.DenseNonreal

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillL2Radicand_eq_gap_polynomial_mul_deflated_sq
    (k : ℕ) (hk : 1 ≤ k) (E : ℂ) (hE : E ∈ hillGapFilledDomain q hq hr k) :
    hillL2Radicand (SpectralWeight.one.toCoeff q) E =
      (E-(hillRealLabels q hq hr (2*k-1) : ℂ))*(E-(hillRealLabels q hq hr (2*k) : ℂ))*
        hillDeflatedEnergyCanonicalRoot q hq hr k E^2 := by
  let F : ℂ → ℂ := fun z => (z-(hillRealLabels q hq hr (2*k-1) : ℂ))*
    (z-(hillRealLabels q hq hr (2*k) : ℂ))*hillDeflatedEnergyCanonicalRoot q hq hr k z^2
  have hF : ContinuousOn F (hillGapFilledDomain q hq hr k) :=
    (((continuous_id.sub continuous_const).mul (continuous_id.sub continuous_const)).continuousOn).mul
      ((analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k).continuousOn.pow 2)
  have hR : ContinuousOn (hillL2Radicand (SpectralWeight.one.toCoeff q)) (hillGapFilledDomain q hq hr k) :=
    (analyticOnNhd_hillL2Radicand _).continuousOn.mono (subset_univ _)
  have he := continuous_eqOn_of_dense_on_open {z : ℂ | z.im ≠ 0} (hillGapFilledDomain q hq hr k)
    dense_complex_nonreal (isOpen_hillGapFilledDomain q hq hr k)
    (hillL2Radicand (SpectralWeight.one.toCoeff q)) F hR hF (by
      intro z hz
      rw [← hillEnergyCanonicalRootProduct_sq_actual q hq hr z (Or.inl hz.2),
        hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated q hq hr k hk z,mul_pow,
        endpointRoot_sq _ _ z (by
          intro hseg
          exact hz.2 (im_eq_zero_of_mem_real_segment _ _ z hseg))])
  exact he hE

end NLS.KdV
