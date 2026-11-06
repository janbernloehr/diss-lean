import NLS.KdV.HillAbelianComplexPeriods

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem analyticOnNhd_hillAbelianComplexPeriod_of_domain
    (n k : ℕ) (hk : 1 ≤ k) (U : Set (Coeff 2)) (hU : IsOpen U)
    (hcircle : ∀ p ∈ U, ∀ z ∈ sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      (z,p) ∈ hillAbelianComplexRootDomain q hq hr) :
    AnalyticOnNhd ℂ (hillAbelianComplexPeriod q hq hr n k) (univ ×ˢ U) := by
  let J : ℂ × (Coeff 2 × Coeff 2) → ℂ × Coeff 2 := fun v => (v.1,v.2.2)
  let K : ℂ × (Coeff 2 × Coeff 2) → ℂ × Coeff 2 := fun v => (v.1,v.2.1)
  let D := J ⁻¹' hillAbelianComplexRootDomain q hq hr
  let F : ℂ × (Coeff 2 × Coeff 2) → ℂ := fun v =>
    hillAbelianHilbertPsi n (K v)/hillAbelianComplexRoot q hq hr (J v)
  have hJ : AnalyticOnNhd ℂ J univ := by
    intro v _
    exact analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hK : AnalyticOnNhd ℂ K univ := by
    intro v _
    exact analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have hD : IsOpen D := (isOpen_hillAbelianComplexRootDomain q hq hr).preimage
    (continuousOn_univ.mp hJ.continuousOn)
  have hF : AnalyticOnNhd ℂ F D := by
    intro v hv
    have hn := (analyticOnNhd_hillAbelianHilbertPsi n (K v) (mem_univ _)).comp (hK v (mem_univ _))
    have hd := (analyticOnNhd_hillAbelianComplexRoot q hq hr (J v) hv).comp (hJ v (mem_univ _))
    exact hn.div hd (hillAbelianComplexRoot_ne_zero q hq hr (J v) hv)
  have hR := add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1.le
  have hc := analyticOnNhd_circleIntegral_of_jointAnalytic F hD hF
    (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k + hillRealGapCollar q hq hr k) hR
    (isOpen_univ.prod hU)
    (fun t ht z hz => hcircle t.2 ht.2 z hz)
  exact analyticOnNhd_const.mul hc

end NLS.KdV
