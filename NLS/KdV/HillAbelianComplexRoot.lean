import NLS.KdV.HillEnergyRootIdentification

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillEnergyCanonicalRootProduct_sq_actual (z : ℂ) (hz : z ∈ hillL2RealCutDomain q hq hr) :
    hillEnergyCanonicalRootProduct q hq hr z^2 = hillL2Radicand (SpectralWeight.one.toCoeff q) z := by
  rw [hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr hz]
  exact hillL2RealCutRoot_sq q hq hr z

theorem hillL2Radicand_ne_zero_on_realCutDomain (z : ℂ) (hz : z ∈ hillL2RealCutDomain q hq hr) :
    hillL2Radicand (SpectralWeight.one.toCoeff q) z ≠ 0 := by
  rw [← hillEnergyCanonicalRootProduct_sq_actual q hq hr z hz]
  exact pow_ne_zero 2 (hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr z hz)

def hillAbelianComplexRootRatio (t : ℂ × Coeff 2) : ℂ :=
  hillL2Radicand t.2 t.1 / hillL2Radicand (SpectralWeight.one.toCoeff q) t.1

theorem analyticOnNhd_hillAbelianComplexRootRatio :
    AnalyticOnNhd ℂ (hillAbelianComplexRootRatio q)
      (hillL2RealCutDomain q hq hr ×ˢ univ) := by
  intro t ht
  have hd : AnalyticAt ℂ (fun v : ℂ × Coeff 2 =>
      hillL2Radicand (SpectralWeight.one.toCoeff q) v.1) t :=
    (analyticOnNhd_hillL2Radicand _ t.1 (mem_univ _)).comp analyticAt_fst
  exact (analyticOnNhd_hillL2Radicand_joint t (mem_univ _)).div hd
    (hillL2Radicand_ne_zero_on_realCutDomain q hq hr t.1 ht.1)

def hillAbelianComplexRootDomain : Set (ℂ × Coeff 2) :=
  (hillL2RealCutDomain q hq hr ×ˢ univ) ∩ (hillAbelianComplexRootRatio q) ⁻¹' slitPlane

theorem isOpen_hillAbelianComplexRootDomain : IsOpen (hillAbelianComplexRootDomain q hq hr) :=
  (analyticOnNhd_hillAbelianComplexRootRatio q hq hr).continuousOn.isOpen_inter_preimage
    ((isOpen_hillL2RealCutDomain q hq hr).prod isOpen_univ) Complex.isOpen_slitPlane

theorem mem_hillAbelianComplexRootDomain_base (z : ℂ) (hz : z ∈ hillL2RealCutDomain q hq hr) :
    (z,SpectralWeight.one.toCoeff q) ∈ hillAbelianComplexRootDomain q hq hr := by
  refine ⟨⟨hz,mem_univ _⟩,?_⟩
  change hillL2Radicand (SpectralWeight.one.toCoeff q) z /
    hillL2Radicand (SpectralWeight.one.toCoeff q) z ∈ slitPlane
  rw [div_self (hillL2Radicand_ne_zero_on_realCutDomain q hq hr z hz)]
  exact one_mem_slitPlane

def hillAbelianComplexRoot (t : ℂ × Coeff 2) : ℂ :=
  hillEnergyCanonicalRootProduct q hq hr t.1 * Complex.sqrt (hillAbelianComplexRootRatio q t)

theorem analyticOnNhd_hillAbelianComplexRoot :
    AnalyticOnNhd ℂ (hillAbelianComplexRoot q hq hr) (hillAbelianComplexRootDomain q hq hr) := by
  intro t ht
  have hb : AnalyticAt ℂ (fun v : ℂ × Coeff 2 => hillEnergyCanonicalRootProduct q hq hr v.1) t :=
    (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr t.1 ht.1.1).comp analyticAt_fst
  have hs := Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds ht.2)
  exact hb.mul (hs.comp (analyticOnNhd_hillAbelianComplexRootRatio q hq hr t ht.1))

theorem hillAbelianComplexRoot_base (z : ℂ) (hz : z ∈ hillL2RealCutDomain q hq hr) :
    hillAbelianComplexRoot q hq hr (z,SpectralWeight.one.toCoeff q) =
      hillEnergyCanonicalRootProduct q hq hr z := by
  unfold hillAbelianComplexRoot hillAbelianComplexRootRatio
  rw [div_self (hillL2Radicand_ne_zero_on_realCutDomain q hq hr z hz)]
  simp only [Complex.sqrt_one,mul_one]

theorem hillAbelianComplexRoot_sq (t : ℂ × Coeff 2)
    (ht : t ∈ hillAbelianComplexRootDomain q hq hr) :
    hillAbelianComplexRoot q hq hr t^2 = hillL2Radicand t.2 t.1 := by
  have hs : (Complex.sqrt (hillAbelianComplexRootRatio q t))^2 = hillAbelianComplexRootRatio q t := by
    have h := Complex.cpow_nat_inv_pow (hillAbelianComplexRootRatio q t) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  rw [hillAbelianComplexRoot,mul_pow,hillEnergyCanonicalRootProduct_sq_actual q hq hr t.1 ht.1.1,hs,
    hillAbelianComplexRootRatio]
  exact mul_div_cancel₀ _ (hillL2Radicand_ne_zero_on_realCutDomain q hq hr t.1 ht.1.1)

theorem hillAbelianComplexRoot_ne_zero (t : ℂ × Coeff 2)
    (ht : t ∈ hillAbelianComplexRootDomain q hq hr) : hillAbelianComplexRoot q hq hr t ≠ 0 := by
  apply mul_ne_zero (hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr t.1 ht.1.1)
  intro he
  have hs : (Complex.sqrt (hillAbelianComplexRootRatio q t))^2 = hillAbelianComplexRootRatio q t := by
    have h := Complex.cpow_nat_inv_pow (hillAbelianComplexRootRatio q t) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  rw [he,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
  exact zero_notMem_slitPlane (hs.symm ▸ ht.2)

end NLS.KdV
