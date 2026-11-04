import NLS.KdV.HillAbelianCoordinateAnalytic
import NLS.KdV.HillFreeAbelianNormalization
import NLS.KdV.FreeFrequencyPsi
/-! # Free normalization of the actual Abelian coordinate factors -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillGapCriticalPoint_free (n : ℕ) (hn : 1≤n) :
    hillGapCriticalPoint 0 hq hr n=freeHillValue n := by
  obtain ⟨hl,hu⟩ := hillFreeGapEndpoints hq hr n hn
  have hs := (hillGapCriticalPoint_spec 0 hq hr n hn).1
  rw [hl,hu] at hs
  exact le_antisymm hs.2 hs.1

theorem hillEnergyCriticalRootRatio_free (n : ℕ) (hn : 1≤n) (z : ℂ)
    (hz : z≠(freeHillValue n : ℂ)) :
    hillEnergyCriticalRootRatio 0 hq hr n z=1 := by
  obtain ⟨hl,hu⟩ := hillFreeGapEndpoints hq hr n hn
  unfold hillEnergyCriticalRootRatio
  rw [hillGapCriticalPoint_free hq hr n hn,hl,hu]
  have he : endpointRoot (freeHillValue n : ℂ) (freeHillValue n : ℂ) z=(freeHillValue n : ℂ)-z := by
    unfold endpointRoot
    rw [sub_self,zero_pow (by norm_num : (2:ℕ)≠0),normalizedStandardRoot_zeroGap]
    congr 1
    ring
  rw [he,div_self (sub_ne_zero.mpr hz.symm)]

theorem hillEnergyChi_free (n : ℕ) (z : ℂ)
    (hz : z∈hillGapFilledDomain 0 hq hr n) :
    hillEnergyChi 0 hq hr n z=(Complex.sqrt z)⁻¹ := by
  have hfactor (k : ℕ) : hillOmittedEnergyCriticalRootFactor 0 hq hr n k z=1 := by
    unfold hillOmittedEnergyCriticalRootFactor
    split_ifs with hk
    · rfl
    · apply hillEnergyCriticalRootRatio_free hq hr (k+1) (by omega)
      intro he
      have hnot := not_mem_other_gap_of_mem_hillGapFilledDomain 0 hq hr n (k+1) (by omega) hk z hz
      apply hnot
      rw [he,(hillFreeGapEndpoints hq hr (k+1) (by omega)).1]
      exact left_mem_segment ℝ _ _
  unfold hillEnergyChi hillOmittedEnergyCriticalRootProduct
  simp only [hfactor,tprod_one,mul_one,hillRealLabels_zero_ground,ofReal_zero,sub_zero]

theorem hillActionGapRatio_free (n : ℕ) (hn : 1≤n) :
    hillActionGapRatio 0 hq hr n=(2*(n:ℂ)*Real.pi)⁻¹ := by
  obtain ⟨hl,hu⟩ := hillFreeGapEndpoints hq hr n hn
  have hcoll := hl.trans hu.symm
  rw [hillActionGapRatio_at_collapse 0 hq hr n hn hcoll]
  have hz : (hillRealLabels 0 hq hr (2*n-1) : ℂ)∈hillGapFilledDomain 0 hq hr n :=
    hillGapSegment_subset_filledDomain 0 hq hr n hn (left_mem_segment ℝ _ _)
  rw [hillEnergyChi_free hq hr n _ hz,hl]
  rw [hillFreeGap_sqrt]
  field_simp

theorem hillAbelianAmplitudePrefactor_free (n : ℕ) (hn : 1≤n) :
    hillAbelianAmplitudePrefactor 0 hq hr n=
      (Real.sqrt (2*(n:ℝ)*Real.pi):ℂ)⁻¹ := by
  have hratio : hillActionGapRatio 0 hq hr n=(((2*(n:ℝ)*Real.pi)⁻¹:ℝ):ℂ) := by
    rw [hillActionGapRatio_free hq hr n hn]
    simp
  rw [hillAbelianAmplitudePrefactor,hillActionGapPrefactor,hratio,ofReal_re,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤2),Real.sqrt_inv,ofReal_mul,ofReal_inv]
  have hs : (Real.sqrt 2:ℂ)≠0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  field_simp

theorem hillDeflatedEnergyCanonicalRoot_free_center (n : ℕ) (hn : 1≤n) :
    hillDeflatedEnergyCanonicalRoot 0 hq hr n (freeHillValue n)=
      I*(-1:ℂ)^n/((n:ℂ)*Real.pi) := by
  let ν : ℕ+ := ⟨n,by omega⟩
  let a : ℂ := freeHillValue n
  have he : freeHillEnergy ν=a := by
    change (((((n:ℝ)*Real.pi)^2):ℝ):ℂ)=((Real.pi^2*(n:ℝ)^2:ℝ):ℂ)
    push_cast
    ring
  have htrace : hillL2Discriminant (SpectralWeight.one.toCoeff
      (0 : WeightedCoeff SpectralWeight.one.toWeight 2))=classicalHillDiscriminant 0 := by
    funext E
    rw [map_zero,hillL2Discriminant_zero,classicalHillDiscriminant_zero]
  have hzero : deriv (classicalHillDiscriminant 0) a=0 := by
    rw [← he]
    exact deriv_classicalHillDiscriminant_free_energy ν
  have hsecond : deriv (deriv (classicalHillDiscriminant 0)) a=
      -((-1:ℂ)^n)/(2*((n:ℂ)*Real.pi)^2) := by
    rw [← he,deriv_deriv_classicalHillDiscriminant_free_energy]
    rfl
  have ha : a∈hillGapFilledDomain 0 hq hr n := by
    rw [show a=(hillRealLabels 0 hq hr (2*n-1):ℂ) by rw [(hillFreeGapEndpoints hq hr n hn).1]]
    exact hillGapSegment_subset_filledDomain 0 hq hr n hn (left_mem_segment ℝ _ _)
  let B := hillDeflatedEnergyCanonicalRoot 0 hq hr n
  have hBa : AnalyticAt ℂ B a := analyticOnNhd_hillDeflatedEnergyCanonicalRoot 0 hq hr n a ha
  have hBn : B a≠0 := hillDeflatedEnergyCanonicalRoot_ne_zero 0 hq hr n hn a ha
  have hd := ((analyticOnNhd_classicalHillDiscriminant 0 a (mem_univ _)).deriv.differentiableAt.hasDerivAt).div
    hBa.differentiableAt.hasDerivAt hBn
  have hH : deriv (hillDeflatedTraceNumerator 0 hq hr n) a=
      deriv (deriv (classicalHillDiscriminant 0)) a/B a := by
    change deriv (fun E => deriv (hillL2Discriminant (SpectralWeight.one.toCoeff
      (0 : WeightedCoeff SpectralWeight.one.toWeight 2))) E/B E) a=_
    rw [htrace]
    change deriv (deriv (classicalHillDiscriminant 0)/B) a=_
    rw [hd.deriv,hzero]
    field_simp
    ring
  have hchi := neg_I_mul_deriv_hillDeflatedTraceNumerator_at_closed_gap 0 hq hr n hn
    ((hillFreeGapEndpoints hq hr n hn).1.trans (hillFreeGapEndpoints hq hr n hn).2.symm)
  rw [(hillFreeGapEndpoints hq hr n hn).1] at hchi
  change -I*deriv (hillDeflatedTraceNumerator 0 hq hr n) a=hillEnergyChi 0 hq hr n a/2 at hchi
  rw [hH,hsecond,hillEnergyChi_free hq hr n a ha,hillFreeGap_sqrt] at hchi
  have hn0 : (n:ℂ)≠0 := by exact_mod_cast (by omega : n≠0)
  have hpi : (Real.pi:ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  change B a=_
  field_simp [hBn,hn0,hpi] at hchi ⊢
  linear_combination -hchi

theorem hillSummedRegularAbelianCorrection_free (n : ℕ) (hn : 1≤n) :
    hillSummedRegularAbelianCorrection 0 hq hr n hn=0 := by
  have ht (k : ℕ) : hillRegularAbelianCorrection 0 hq hr n hn (k+1) (by omega)=0 := by
    apply hillRegularAbelianCorrection_closed
    dsimp only [hillRealGapHalfLength]
    rw [(hillFreeGapEndpoints hq hr (k+1) (by omega)).1,
      (hillFreeGapEndpoints hq hr (k+1) (by omega)).2]
    simp
  simp only [hillSummedRegularAbelianCorrection,ht,tsum_zero]
end NLS.KdV
