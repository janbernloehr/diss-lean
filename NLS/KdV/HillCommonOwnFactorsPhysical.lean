import NLS.KdV.HillCommonComplexOwnFactors
import NLS.KdV.HillOwnGapFactor
import NLS.KdV.HillUniformDirichletPhysical
import NLS.KdV.HillFilledFreeGapPhysical

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

omit h0q h0r in
theorem conj_hillOwnGapFactor
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (k : ℕ) (hk : 1≤k) :
    (starRingEnd ℂ) (hillOwnGapFactor q hq hr k hk)=
      (hillRealGapCenter q hq hr k:ℂ)-(hillDirichletEnergy q hq hr k hk:ℂ)-
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr k hk)/
          hillDeflatedEnergyCanonicalRoot q hq hr k (hillDirichletEnergy q hq hr k hk) := by
  have hreal := hillDeflatedEnergyCanonicalRoot_re_eq_zero_on_gap q hq hr k hk
    (hillDirichletEnergy q hq hr k hk) (hillDirichletEnergy_mem_gap q hq hr k hk)
  have hroot : (starRingEnd ℂ) (hillDeflatedEnergyCanonicalRoot q hq hr k (hillDirichletEnergy q hq hr k hk)) =
      -hillDeflatedEnergyCanonicalRoot q hq hr k (hillDirichletEnergy q hq hr k hk) := by
    apply Complex.ext <;> simp only [Complex.conj_re,Complex.conj_im,neg_re,neg_im,hreal,neg_zero]
  have hsheet : (starRingEnd ℂ) (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q)
      (hillDirichletEnergy q hq hr k hk))=hillDirichletSheetRoot (SpectralWeight.one.toCoeff q)
      (hillDirichletEnergy q hq hr k hk) := by
    rw [hillDirichletSheetRoot_at_dirichlet_eq_norming q hq hr k hk]
    exact Complex.conj_ofReal _
  simp only [hillOwnGapFactor,map_add,map_sub,map_div₀,Complex.conj_ofReal,hsheet,hroot,div_neg]
  ring

theorem exists_hillComplexOwnGapFactors_bounded_real_physical_matching (B : ℝ) :
    ∃ N : ℕ, ∃ hN : 1≤N, ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2,
      ∀ hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0,
      ∀ hr : IsRealHillPotential (SpectralWeight.one.toCoeff q), ‖SpectralWeight.one.toCoeff q‖≤B →
        ∀ k : ℕ, ∀ hk : N≤k,
          hillComplexOwnGapFactor h0q h0r k (SpectralWeight.one.toCoeff q)=
            hillOwnGapFactor q hq hr k (hN.trans hk) ∧
          hillComplexOwnGapDualFactor h0q h0r k (SpectralWeight.one.toCoeff q)=
            (starRingEnd ℂ) (hillOwnGapFactor q hq hr k (hN.trans hk)) := by
  obtain ⟨Nm,hNm,hm⟩ := exists_hillFreeGap_bounded_real_symmetric_data_matching h0q h0r B
  obtain ⟨Nd,hNd,hd⟩ := exists_hillScaledDirichletRoot_bounded_real_physical_matching h0q h0r (1/16) (by norm_num) (by norm_num) B
  obtain ⟨Nr,hNr,hr⟩ := exists_hillFilledFreeGapRoot_bounded_real_physical_matching h0q h0r B
  obtain ⟨Nc,hNc,hc⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart h0q h0r (1/16) (by norm_num) (by norm_num) B
  refine ⟨Nm+Nd+Nr+Nc,hNm.trans (by omega),?_⟩
  intro q hq hreal hp k hk
  have hkm : Nm≤k := by omega
  have hkd : Nd≤k := by omega
  have hkr : Nr≤k := by omega
  have hkc : Nc≤k := by omega
  have hk1 := hNm.trans hkm
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hμ := ((hc k hkc).2 (SpectralWeight.one.toCoeff q) hp).1
  have hμR : hillScaledDirichletRoot h0q h0r (1/16) k (SpectralWeight.one.toCoeff q) ∈
      closedBall (hillRealGapCenter 0 h0q h0r k : ℂ) R :=
    closedBall_subset_closedBall (by linarith : (1/16)*R≤R) (ball_subset_closedBall hμ)
  constructor
  · rw [hillComplexOwnGapFactor,hillComplexDirichletGapTerminal,(hm q hq hreal hp k hkm).1,
      hr q hq hreal hp k hkr _ hμR,hd q hq hreal hp k hkd]
    rfl
  · rw [hillComplexOwnGapDualFactor,hillComplexDirichletGapTerminal,(hm q hq hreal hp k hkm).1,
      hr q hq hreal hp k hkr _ hμR,hd q hq hreal hp k hkd]
    exact (conj_hillOwnGapFactor q hq hreal k hk1).symm

end NLS.KdV
