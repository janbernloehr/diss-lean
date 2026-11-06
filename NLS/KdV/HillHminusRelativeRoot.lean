import NLS.KdV.HillAbelianComplexRoot
import NLS.KdV.HillHminusOriginalSheets

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillHminusRelativeRootRatio (t : ℂ × PeriodOneHminusOne) : ℂ :=
  hillHminusRadicand t.2 t.1 / hillL2Radicand (SpectralWeight.one.toCoeff q) t.1

theorem analyticOnNhd_hillHminusRelativeRootRatio :
    AnalyticOnNhd ℂ (hillHminusRelativeRootRatio q)
      (hillL2RealCutDomain q hq hr ×ˢ univ) := by
  intro t ht
  have hd : AnalyticAt ℂ (fun v : ℂ × PeriodOneHminusOne =>
      hillL2Radicand (SpectralWeight.one.toCoeff q) v.1) t :=
    (analyticOnNhd_hillL2Radicand _ t.1 (mem_univ _)).comp analyticAt_fst
  exact (analyticOnNhd_hillHminusRadicand_joint t (mem_univ _)).div hd
    (hillL2Radicand_ne_zero_on_realCutDomain q hq hr t.1 ht.1)

def hillHminusRelativeRootDomain : Set (ℂ × PeriodOneHminusOne) :=
  (hillL2RealCutDomain q hq hr ×ˢ univ) ∩ (hillHminusRelativeRootRatio q) ⁻¹' slitPlane

theorem isOpen_hillHminusRelativeRootDomain : IsOpen (hillHminusRelativeRootDomain q hq hr) :=
  (analyticOnNhd_hillHminusRelativeRootRatio q hq hr).continuousOn.isOpen_inter_preimage
    ((isOpen_hillL2RealCutDomain q hq hr).prod isOpen_univ) Complex.isOpen_slitPlane

theorem mem_hillHminusRelativeRootDomain_base (z : ℂ) (hz : z ∈ hillL2RealCutDomain q hq hr) :
    (z,hillOriginalHminusSource q) ∈ hillHminusRelativeRootDomain q hq hr := by
  refine ⟨⟨hz,mem_univ _⟩,?_⟩
  change hillHminusRadicand (hillOriginalHminusSource q) z /
    hillL2Radicand (SpectralWeight.one.toCoeff q) z ∈ slitPlane
  rw [hillHminusRadicand_original_source_agreement q hq,
    div_self (hillL2Radicand_ne_zero_on_realCutDomain q hq hr z hz)]
  exact one_mem_slitPlane

def hillHminusRelativeRoot (t : ℂ × PeriodOneHminusOne) : ℂ :=
  hillEnergyCanonicalRootProduct q hq hr t.1 * Complex.sqrt (hillHminusRelativeRootRatio q t)

theorem analyticOnNhd_hillHminusRelativeRoot :
    AnalyticOnNhd ℂ (hillHminusRelativeRoot q hq hr) (hillHminusRelativeRootDomain q hq hr) := by
  intro t ht
  have hb : AnalyticAt ℂ (fun v : ℂ × PeriodOneHminusOne => hillEnergyCanonicalRootProduct q hq hr v.1) t :=
    (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr t.1 ht.1.1).comp analyticAt_fst
  have hs := Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds ht.2)
  exact hb.mul (hs.comp (analyticOnNhd_hillHminusRelativeRootRatio q hq hr t ht.1))

theorem hillHminusRelativeRoot_base (z : ℂ) (hz : z ∈ hillL2RealCutDomain q hq hr) :
    hillHminusRelativeRoot q hq hr (z,hillOriginalHminusSource q) =
      hillEnergyCanonicalRootProduct q hq hr z := by
  unfold hillHminusRelativeRoot hillHminusRelativeRootRatio
  rw [hillHminusRadicand_original_source_agreement q hq,
    div_self (hillL2Radicand_ne_zero_on_realCutDomain q hq hr z hz)]
  simp only [Complex.sqrt_one,mul_one]

theorem hillHminusRelativeRoot_sq (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ hillHminusRelativeRootDomain q hq hr) :
    hillHminusRelativeRoot q hq hr t^2 = hillHminusRadicand t.2 t.1 := by
  have hs : (Complex.sqrt (hillHminusRelativeRootRatio q t))^2 = hillHminusRelativeRootRatio q t := by
    have h := Complex.cpow_nat_inv_pow (hillHminusRelativeRootRatio q t) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  rw [hillHminusRelativeRoot,mul_pow,hillEnergyCanonicalRootProduct_sq_actual q hq hr t.1 ht.1.1,hs,
    hillHminusRelativeRootRatio]
  exact mul_div_cancel₀ _ (hillL2Radicand_ne_zero_on_realCutDomain q hq hr t.1 ht.1.1)

theorem hillHminusRelativeRoot_ne_zero (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ hillHminusRelativeRootDomain q hq hr) : hillHminusRelativeRoot q hq hr t ≠ 0 := by
  apply mul_ne_zero (hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr t.1 ht.1.1)
  intro he
  have hs : (Complex.sqrt (hillHminusRelativeRootRatio q t))^2 = hillHminusRelativeRootRatio q t := by
    have h := Complex.cpow_nat_inv_pow (hillHminusRelativeRootRatio q t) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  rw [he,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
  exact zero_notMem_slitPlane (hs.symm ▸ ht.2)

/-- On every original even L2 source this is exactly the already checked
relative physical root, with the same chosen sign. -/
theorem hillHminusRelativeRoot_original_source
    (p : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hp : SpectralWeight.one.toCoeff p ∈ Coeff.paritySubspace 0) (z : ℂ) :
    hillHminusRelativeRoot q hq hr (z,hillOriginalHminusSource p) =
      hillAbelianComplexRoot q hq hr (z,SpectralWeight.one.toCoeff p) := by
  simp only [hillHminusRelativeRoot,hillHminusRelativeRootRatio,
    hillAbelianComplexRoot,hillAbelianComplexRootRatio,
    hillHminusRadicand_original_source_agreement p hp]

theorem hillHminusRelativeRootDomain_original_source_iff
    (p : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hp : SpectralWeight.one.toCoeff p ∈ Coeff.paritySubspace 0) (z : ℂ) :
    (z,hillOriginalHminusSource p) ∈ hillHminusRelativeRootDomain q hq hr ↔
      (z,SpectralWeight.one.toCoeff p) ∈ hillAbelianComplexRootDomain q hq hr := by
  simp only [hillHminusRelativeRootDomain,hillHminusRelativeRootRatio,
    hillAbelianComplexRootDomain,hillAbelianComplexRootRatio,
    mem_inter_iff,mem_prod,mem_univ,and_true,mem_preimage,
    hillHminusRadicand_original_source_agreement p hp]

end NLS.KdV
