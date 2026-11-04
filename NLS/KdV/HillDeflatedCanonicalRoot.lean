import NLS.KdV.HillOmittedEnergyRootNonvanishing

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



def hillDeflatedEnergyCanonicalRoot
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ) : ℂ :=
  (-2*I/(freeHillValue n : ℂ))*Complex.sqrt (z-hillRealLabels q hq hr 0)*
    hillOmittedEnergyRootProduct q hq hr n z

theorem analyticOnNhd_hillDeflatedEnergyCanonicalRoot
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) :
    AnalyticOnNhd ℂ (hillDeflatedEnergyCanonicalRoot q hq hr n) (hillGapFilledDomain q hq hr n) := by
  intro z hz
  have hs : AnalyticAt ℂ Complex.sqrt (z-hillRealLabels q hq hr 0) :=
    Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds
      (hillGroundShift_mem_slitPlane_of_mem_filledDomain q hq hr n z hz))
  have hc := hs.comp (f := fun w : ℂ => w-hillRealLabels q hq hr 0)
    (analyticAt_id.sub analyticAt_const)
  exact (analyticAt_const.mul hc).mul
    (analyticOnNhd_hillOmittedEnergyRootProduct q hq hr n z hz)

theorem hillDeflatedEnergyCanonicalRoot_ne_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ hillGapFilledDomain q hq hr n) :
    hillDeflatedEnergyCanonicalRoot q hq hr n z ≠ 0 := by
  have hden : (freeHillValue n : ℂ) ≠ 0 := by
    simpa only [Nat.sub_add_cancel hn] using hillGapRootEnergyFactor_denominator_ne_zero (n-1)
  have hzero : z-(hillRealLabels q hq hr 0 : ℂ) ≠ 0 := by
    intro he
    have hs := hillGroundShift_mem_slitPlane_of_mem_filledDomain q hq hr n z hz
    rw [he] at hs
    exact Complex.zero_notMem_slitPlane hs
  have hs : (Complex.sqrt (z-hillRealLabels q hq hr 0))^2 = z-hillRealLabels q hq hr 0 := by
    have h := Complex.cpow_nat_inv_pow (z-hillRealLabels q hq hr 0) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hroot : Complex.sqrt (z-hillRealLabels q hq hr 0) ≠ 0 := by
    intro he
    rw [he,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
    exact hzero hs.symm
  exact mul_ne_zero
    (mul_ne_zero (div_ne_zero (by norm_num : (-2*I : ℂ) ≠ 0) hden) hroot)
    (hillOmittedEnergyRootProduct_ne_zero q hq hr n z hz)

theorem hillEnergyRootProduct_eq_selected_mul_omitted
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    hillEnergyRootProduct q hq hr z =
      hillEnergyRootFactor q hq hr n z*hillOmittedEnergyRootProduct q hq hr n z := by
  let f : ℕ → ℂ := fun k => hillEnergyRootFactor q hq hr (k+1) z
  have hi (k : ℕ) : (if k = n-1 then 1 else f k) =
      hillOmittedEnergyRootFactor q hq hr n k z := by
    unfold hillOmittedEnergyRootFactor
    have he : k = n-1 ↔ k+1 = n := by omega
    simp only [he,f]
  have hup : Function.update f (n-1) 1 =
      fun k => hillOmittedEnergyRootFactor q hq hr n k z := by
    funext k
    rw [Function.update_apply]
    exact hi k
  have hm : Multipliable (Function.update f (n-1) 1) := by
    rw [hup]
    exact multipliable_hillOmittedEnergyRootFactors q hq hr n z
  have hp := Multipliable.tprod_eq_mul_tprod_ite' (f := f) (n-1) hm
  simp_rw [hi] at hp
  simpa only [f,hillEnergyRootProduct,hillOmittedEnergyRootProduct,Nat.sub_add_cancel hn] using hp

theorem hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    hillEnergyCanonicalRootProduct q hq hr z =
      endpointRoot (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) z*
        hillDeflatedEnergyCanonicalRoot q hq hr n z := by
  rw [hillEnergyCanonicalRootProduct,hillEnergyRootProduct_eq_selected_mul_omitted q hq hr n hn z,
    hillEnergyRootFactor,hillDeflatedEnergyCanonicalRoot]
  ring

end NLS.KdV
