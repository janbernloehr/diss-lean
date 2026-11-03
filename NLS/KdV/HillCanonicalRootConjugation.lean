import NLS.KdV.HillPhysicalRootSourceIdentification
import NLS.KdV.HillL2PrimitiveReflection

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem mem_hillL2RealCutDomain_conj (E : ℂ) (hE : E ∈ hillL2RealCutDomain q hq hr) :
    conj E ∈ hillL2RealCutDomain q hq hr := by
  rcases hE with hi | ⟨j,hj⟩
  · exact Or.inl (by simpa only [conj_im,neg_ne_zero] using hi)
  · exact Or.inr ⟨j,by simpa only [conj_re] using hj⟩

theorem hillEnergyCanonicalRootProduct_conj (E : ℂ) (hE : E ∈ hillL2RealCutDomain q hq hr) :
    hillEnergyCanonicalRootProduct q hq hr (conj E) = -conj (hillEnergyCanonicalRootProduct q hq hr E) := by
  let S := hillL2RealCutDomain q hq hr
  have hconj : MapsTo conj S S := fun E hE => mem_hillL2RealCutDomain_conj q hq hr E hE
  have hc := (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr).continuousOn
  have hf : ContinuousOn (fun E => hillEnergyCanonicalRootProduct q hq hr (conj E)) S :=
    hc.comp continuous_conj.continuousOn hconj
  have hg : ContinuousOn (fun E => -conj (hillEnergyCanonicalRootProduct q hq hr E)) S :=
    (continuous_conj.comp_continuousOn hc).neg
  have he := continuous_eqOn_of_dense_on_open {E : ℂ | E.im ≠ 0} S dense_complex_nonreal
    (isOpen_hillL2RealCutDomain q hq hr) _ _ hf hg (by
      intro z hz
      dsimp only []
      have hznonreal : z.im ≠ 0 := hz.2
      rw [hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr (hconj hz.1),
        hillL2RealCutRoot_eq_source q hq hr (conj z) (by simpa only [conj_im,neg_ne_zero] using hznonreal),
        hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr hz.1,
        hillL2RealCutRoot_eq_source q hq hr z hznonreal,
        hillL2ContinuedRoot_conj _ hr z (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hznonreal)])
  exact he hE

end NLS.KdV
