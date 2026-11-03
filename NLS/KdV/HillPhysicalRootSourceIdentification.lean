import NLS.KdV.HillEnergyRootIdentification
import NLS.ComplexAnalysis.DenseNonreal

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem hillEnergyCanonicalRootProduct_eq_continued_of_mem
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (E : ℂ)
    (hcut : E ∈ hillL2RealCutDomain q hq hr)
    (hsource : (E,SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain) :
    hillEnergyCanonicalRootProduct q hq hr E = hillL2ContinuedRoot (E,SpectralWeight.one.toCoeff q) := by
  let J : ℂ → ℂ × Coeff 2 := fun z => (z,SpectralWeight.one.toCoeff q)
  let S := hillL2RealCutDomain q hq hr ∩ J ⁻¹' hillL2ContinuationDomain
  have hJ : Continuous J := continuous_id.prodMk continuous_const
  have hS : IsOpen S := (isOpen_hillL2RealCutDomain q hq hr).inter
    (isOpen_hillL2ContinuationDomain.preimage hJ)
  have hc : ContinuousOn (fun z => hillL2ContinuedRoot (J z)) S :=
    analyticOnNhd_hillL2ContinuedRoot.continuousOn.comp hJ.continuousOn (fun _ hz => hz.2)
  have he := continuous_eqOn_of_dense_on_open {z : ℂ | z.im ≠ 0} S dense_complex_nonreal hS
    (hillEnergyCanonicalRootProduct q hq hr) (fun z => hillL2ContinuedRoot (J z))
    ((analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr).continuousOn.mono inter_subset_left)
    hc (by
      intro z hz
      rw [hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr hz.1.1,
        hillL2RealCutRoot_eq_source q hq hr z hz.2])
  exact he ⟨hcut,hsource⟩

end NLS.KdV
