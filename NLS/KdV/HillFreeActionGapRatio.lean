import NLS.KdV.HillActionGapRatioAnalytic
import NLS.KdV.HillFreeAbelianNormalization

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillGapCriticalPoint_zero (k : ℕ) (hk : 1≤k) :
    hillGapCriticalPoint 0 h0q h0r k=freeHillValue k := by
  have h := (hillGapCriticalPoint_spec 0 h0q h0r k hk).1
  obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r k hk
  rw [hl,hu] at h
  exact le_antisymm h.2 h.1

theorem hillOmittedEnergyCriticalRootProduct_zero (n : ℕ) (_hn : 1≤n) (z : ℂ)
    (hz : z∈hillGapFilledDomain 0 h0q h0r n) :
    hillOmittedEnergyCriticalRootProduct 0 h0q h0r n z=1 := by
  have he (k : ℕ) : hillOmittedEnergyCriticalRootFactor 0 h0q h0r n k z=1 := by
    unfold hillOmittedEnergyCriticalRootFactor
    split_ifs with hkn
    · rfl
    · have hnot := not_mem_other_gap_of_mem_hillGapFilledDomain 0 h0q h0r n (k+1) (by omega) hkn z hz
      obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r (k+1) (by omega)
      have hdiff : (freeHillValue (k+1 : ℕ):ℂ)-z≠0 := by
        intro hzero
        apply hnot
        rw [hl,hu,← sub_eq_zero.mp hzero]
        exact left_mem_segment ℝ _ _
      rw [hillEnergyCriticalRootRatio,hillGapCriticalPoint_zero h0q h0r (k+1) (by omega),hl,hu]
      simp only [endpointRoot,normalizedStandardRoot,sub_self,zero_pow (by norm_num : 2≠0),
        zero_div,sub_zero,sqrt_one,mul_one]
      have hc : ((freeHillValue (k+1 : ℕ):ℂ)+(freeHillValue (k+1 : ℕ):ℂ))/2-z=(freeHillValue (k+1 : ℕ):ℂ)-z := by ring
      rw [hc,div_self hdiff]
  simp only [hillOmittedEnergyCriticalRootProduct,he,tprod_one]

theorem hillEnergyChi_zero (n : ℕ) (_hn : 1≤n) (z : ℂ)
    (hz : z∈hillGapFilledDomain 0 h0q h0r n) :
    hillEnergyChi 0 h0q h0r n z=(sqrt z)⁻¹ := by
  rw [hillEnergyChi,hillRealLabels_zero_ground h0q h0r,ofReal_zero,sub_zero,
    hillOmittedEnergyCriticalRootProduct_zero h0q h0r n _hn z hz,mul_one]

theorem hillActionGapRatio_zero (n : ℕ) (hn : 1≤n) :
    hillActionGapRatio 0 h0q h0r n=(2*(n:ℂ)*Real.pi)⁻¹ := by
  obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r n hn
  have hclosed : hillRealLabels 0 h0q h0r (2*n-1)=hillRealLabels 0 h0q h0r (2*n) := hl.trans hu.symm
  have hz : (freeHillValue n:ℂ)∈hillGapFilledDomain 0 h0q h0r n := by
    rw [← hl]
    exact hillGapSegment_subset_filledDomain 0 h0q h0r n hn (left_mem_segment ℝ _ _)
  rw [hillActionGapRatio_at_collapse 0 h0q h0r n hn hclosed,hl,
    hillEnergyChi_zero h0q h0r n hn _ hz,hillFreeGap_sqrt]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end NLS.KdV
