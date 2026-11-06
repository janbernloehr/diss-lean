import NLS.KdV.HillComplexPeriodControl
import NLS.ComplexAnalysis.TraceRootBranchUniqueness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillEnergyCanonicalRootProduct_zero_eq_freeRoot (E : ℂ) :
    hillEnergyCanonicalRootProduct 0 hq hr E = classicalHillFreeRoot E := by
  rw [hillEnergyCanonicalRootProduct_zero,classicalHillFreeRoot,classicalHillFreePrimitive]
  rw [show -I*Complex.sqrt E = -(Complex.sqrt E*I) by ring,sinh_neg,sinh_mul_I]
  ring

theorem hillAbelianComplexRoot_eq_continued_of_radial_domain (E : ℂ) (p : Coeff 2)
    (hE : E ∈ slitPlane)
    (hdom : ∀ s ∈ Icc (0 : ℝ) 1, (E,(s : ℂ) • p) ∈ hillAbelianComplexRootDomain 0 hq hr) :
    hillAbelianComplexRoot 0 hq hr (E,p) = hillL2ContinuedRoot (E,p) := by
  have hsource : (E,p) ∈ hillL2ContinuationDomain := by
    rw [mem_hillL2ContinuationDomain_iff]
    refine ⟨hE,?_⟩
    intro s hs
    rw [← hillAbelianComplexRoot_sq 0 hq hr (E,(s : ℂ) • p) (hdom s hs)]
    exact pow_ne_zero 2 (hillAbelianComplexRoot_ne_zero 0 hq hr _ (hdom s hs))
  have hR : ContinuousOn (fun s : ℝ => hillAbelianComplexRoot 0 hq hr (E,(s : ℂ) • p)) (Icc (0 : ℝ) 1) :=
    (analyticOnNhd_hillAbelianComplexRoot 0 hq hr).continuousOn.comp (by fun_prop) hdom
  have h0cut := (hdom 0 ⟨le_rfl,by norm_num⟩).1.1
  have hbase : hillAbelianComplexRoot 0 hq hr (E,((0 : ℝ) : ℂ) • p) = hillL2SourceFamily.freeRoot E := by
    simp only [ofReal_zero,zero_smul]
    have he := hillAbelianComplexRoot_base 0 hq hr E h0cut
    rw [map_zero] at he
    rw [he,hillEnergyCanonicalRootProduct_zero_eq_freeRoot hq hr]
    rfl
  have he := TracePrimitiveFamily.root_eq_continuous_radial_branch hillL2SourceFamily E p hsource
    (fun s => hillAbelianComplexRoot 0 hq hr (E,(s : ℂ) • p)) hR
    (fun s hs => by
      change hillAbelianComplexRoot 0 hq hr (E,(s : ℂ) • p)^2 = hillL2Radicand ((s : ℂ) • p) E
      exact hillAbelianComplexRoot_sq 0 hq hr _ (hdom s hs)) hbase
  simpa only [hillL2ContinuedRoot,ofReal_one,one_smul] using he.symm

end NLS.KdV
