import NLS.KdV.HillGlobalDifferentialAnalyticExtension

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem continuous_hillAbelianSelectedGlobalPsi_joint (n : ℕ) (hn : 1 ≤ n) :
    Continuous (fun t : ℂ × RealPeriodOneHillPotential =>
      hillAbelianSelectedGlobalPsi t.2.val t.2.property.1 t.2.property.2 n hn t.1) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨G,hG,hmatch⟩ := exists_hillAbelianSelectedGlobalPsi_joint_analytic_extension t.2.val t.2.property.1 t.2.property.2 h0q h0r n hn
  let J : ℂ × RealPeriodOneHillPotential → ℂ × Coeff 2 := fun u => (u.1,SpectralWeight.one.toCoeff u.2.val)
  have hJ : Continuous J := continuous_fst.prodMk
    ((SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val).comp continuous_snd)
  have hGat : ContinuousAt G (J t) := (hG t.1).continuousAt
  have hc : ContinuousAt (fun u : ℂ × RealPeriodOneHillPotential => G (J u)) t :=
    hGat.comp hJ.continuousAt
  have he : (fun u : ℂ × RealPeriodOneHillPotential => G (J u)) =ᶠ[𝓝 t]
      (fun u => hillAbelianSelectedGlobalPsi u.2.val u.2.property.1 u.2.property.2 n hn u.1) := by
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually hmatch] with u hu
    exact hu u.1
  exact hc.congr_of_eventuallyEq he.symm

omit h0q h0r in
theorem continuousOn_hillEnergyCanonicalRootProduct_joint :
    ContinuousOn (fun t : ℂ × RealPeriodOneHillPotential =>
      hillEnergyCanonicalRootProduct t.2.val t.2.property.1 t.2.property.2 t.1) hillRealCutFamilyDomain := by
  intro t ht
  obtain ⟨r,hrpos,V,hV,hqV,hmatch⟩ := exists_hillAbelianComplexRoot_local_physical_matching
    t.2.val t.2.property.1 t.2.property.2 t.1 ht
  let J : ℂ × RealPeriodOneHillPotential → ℂ × Coeff 2 := fun u => (u.1,SpectralWeight.one.toCoeff u.2.val)
  have hJ : Continuous J := continuous_fst.prodMk
    ((SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val).comp continuous_snd)
  have hroot : ContinuousAt (hillAbelianComplexRoot t.2.val t.2.property.1 t.2.property.2) (J t) :=
    (analyticOnNhd_hillAbelianComplexRoot t.2.val t.2.property.1 t.2.property.2 _
      (mem_hillAbelianComplexRootDomain_base t.2.val t.2.property.1 t.2.property.2 t.1 ht)).continuousAt
  have hc : ContinuousAt (fun u : ℂ × RealPeriodOneHillPotential =>
      hillAbelianComplexRoot t.2.val t.2.property.1 t.2.property.2 (J u)) t := hroot.comp hJ.continuousAt
  have he : (fun u : ℂ × RealPeriodOneHillPotential =>
      hillAbelianComplexRoot t.2.val t.2.property.1 t.2.property.2 (J u)) =ᶠ[𝓝 t]
      (fun u => hillEnergyCanonicalRootProduct u.2.val u.2.property.1 u.2.property.2 u.1) := by
    filter_upwards [continuous_fst.continuousAt.tendsto.eventually (ball_mem_nhds t.1 hrpos),
      continuous_snd.continuousAt.tendsto.eventually (hV.mem_nhds hqV)] with u hu1 hu2
    exact (hmatch u.2 hu2 u.1 hu1).2.2
  exact (hc.congr_of_eventuallyEq he.symm).continuousWithinAt

theorem continuousOn_hillNormalizedAbelianDifferential_joint (n : ℕ) (hn : 1 ≤ n) :
    ContinuousOn (fun t : ℂ × RealPeriodOneHillPotential =>
      hillAbelianSelectedGlobalPsi t.2.val t.2.property.1 t.2.property.2 n hn t.1/
        hillEnergyCanonicalRootProduct t.2.val t.2.property.1 t.2.property.2 t.1) hillRealCutFamilyDomain := by
  exact (continuous_hillAbelianSelectedGlobalPsi_joint h0q h0r n hn).continuousOn.div
    continuousOn_hillEnergyCanonicalRootProduct_joint
    (fun t ht => hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain t.2.val t.2.property.1 t.2.property.2 t.1 ht)

end NLS.KdV
