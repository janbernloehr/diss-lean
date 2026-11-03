import NLS.KdV.HillAbelianComplexRoot
import NLS.KdV.HillPhysicalRootSourceIdentification

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelianComplexRoot_eventually_eq_continued_at_nonreal
    (E : ℂ) (hE : E.im ≠ 0) :
    hillAbelianComplexRoot q hq hr =ᶠ[𝓝 (E,SpectralWeight.one.toCoeff q)] hillL2ContinuedRoot := by
  let t0 : ℂ × Coeff 2 := (E,SpectralWeight.one.toCoeff q)
  let D := hillAbelianComplexRootDomain q hq hr ∩ hillL2ContinuationDomain
  have hD : IsOpen D := (isOpen_hillAbelianComplexRootDomain q hq hr).inter isOpen_hillL2ContinuationDomain
  have ht0 : t0 ∈ D := ⟨mem_hillAbelianComplexRootDomain_base q hq hr E (Or.inl hE),
    mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr E hE⟩
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds ht0)
  have hR : ContinuousOn (hillAbelianComplexRoot q hq hr) (ball t0 r) :=
    (analyticOnNhd_hillAbelianComplexRoot q hq hr).continuousOn.mono (fun _ ht => (hball ht).1)
  have hS : ContinuousOn hillL2ContinuedRoot (ball t0 r) :=
    analyticOnNhd_hillL2ContinuedRoot.continuousOn.mono (fun _ ht => (hball ht).2)
  have hbase : hillAbelianComplexRoot q hq hr t0 = hillL2ContinuedRoot t0 := by
    rw [hillAbelianComplexRoot_base q hq hr E (Or.inl hE)]
    exact hillEnergyCanonicalRootProduct_eq_continued_of_mem q hq hr E (Or.inl hE) ht0.2
  have he := (convex_ball t0 r).isPreconnected.eq_of_sq_eq hR hS
    (fun t ht => (hillAbelianComplexRoot_sq q hq hr t (hball ht).1).trans
      (hillL2ContinuedRoot_sq t (hball ht).2).symm)
    (fun {t} ht => hillL2ContinuedRoot_ne_zero t (hball ht).2)
    (mem_ball_self hrpos) hbase
  exact Filter.eventually_of_mem (ball_mem_nhds t0 hrpos) he

end NLS.KdV
