import NLS.KdV.HillNativeWeightedNormingSheet
import NLS.KdV.HillNativeDirichletMidpoint
import NLS.KdV.HillCommonComplexOwnFactors

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Both individual original complex own-gap factors satisfy a genuine
weighted Fourier estimate. This uses separate midpoint and sheet bounds,
and does not infer either factor bound from their product. -/
theorem exists_hillComplexOwnGapFactors_native_weighted_bound (B : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, 1≤N ∧ ∀ w : SpectralWeight,
      ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖≤B → ∀ n : ℕ, N≤n →
      w (2*(n : ℤ))*‖hillComplexOwnGapFactor h0q h0r n (hillPeriodOneCoefficientMap w q)‖ ≤
        C*(w (2*(n : ℤ))*‖q.val n‖+w (2*(n : ℤ))*‖q.val (-(n : ℤ))‖+
          16*‖q‖^2/(n : ℝ)) ∧
      w (2*(n : ℤ))*‖hillComplexOwnGapDualFactor h0q h0r n (hillPeriodOneCoefficientMap w q)‖ ≤
        C*(w (2*(n : ℤ))*‖q.val n‖+w (2*(n : ℤ))*‖q.val (-(n : ℤ))‖+
          16*‖q‖^2/(n : ℝ)) := by
  obtain ⟨C,hC,Ns,hNs,hsheet⟩ := exists_hillNativeComplexDirichletGapTerminal_weighted_bound h0q h0r B hB
  obtain ⟨Nm,hNm,hmid⟩ := exists_hillNativeComplexDirichletMidpointDifference_weighted_bound h0q h0r B hB
  refine ⟨4*B+10+C,by positivity,max Nm Ns,hNm.trans (le_max_left _ _),?_⟩
  intro w q hq n hn
  have hm := hmid w q hq n ((le_max_left _ _).trans hn)
  have hs := hsheet w q hq n ((le_max_right _ _).trans hn)
  let p := hillPeriodOneCoefficientMap w q
  let M := hillNativeComplexDirichletMidpointDifference h0q h0r w n q
  let Y := hillNativeComplexDirichletGapTerminal h0q h0r w n q
  have hp : hillComplexOwnGapFactor h0q h0r n p=M+Y := rfl
  have hd : hillComplexOwnGapDualFactor h0q h0r n p=M-Y := rfl
  have hW : 0≤w (2*(n : ℤ)) := (w.positive _).le
  change w (2*(n : ℤ))*‖M‖≤_ at hm
  change w (2*(n : ℤ))*‖Y‖≤_ at hs
  constructor
  · change w (2*(n : ℤ))*‖hillComplexOwnGapFactor h0q h0r n p‖≤_
    rw [hp]
    have hh := mul_le_mul_of_nonneg_left (norm_add_le M Y) hW
    nlinarith only [hh,hm,hs]
  · change w (2*(n : ℤ))*‖hillComplexOwnGapDualFactor h0q h0r n p‖≤_
    rw [hd]
    have hh := mul_le_mul_of_nonneg_left (norm_sub_le M Y) hW
    nlinarith only [hh,hm,hs]

end NLS.KdV
