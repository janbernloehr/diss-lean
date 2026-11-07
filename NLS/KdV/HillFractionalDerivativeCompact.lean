import NLS.KdV.HillFractionalDerivativeCompatibility
import NLS.SequenceSpaces.FractionalEndpointCompactness

/-! The actual native fractional Fourier derivative defect is compact
at every real source. First use endpoint interpolation at real L2 sources;
then use norm continuity of the strong derivative and Fourier density. -/
noncomputable section
open Filter Topology NLS.WeightedCoeff
namespace NLS.KdV

theorem isCompactOperator_fractionalFourierDefect_at_l2
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev 0) 2)
    (hq : IsRealPeriodOneHminusOne (periodOneL2Inclusion (sobolevToL2 (by norm_num) q))) :
    IsCompactOperator (fderiv ℂ (hillFractionalFourierDefect r hr hr1)
      (sobolevInclusion (show -r ≤ 0 by linarith) q)) := by
  let b := sobolevInclusion (show -r ≤ 0 by linarith) q
  have hb : IsRealPeriodOneHminusOne
      (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b) := by
    rw [fractionalInclusion_l2 r hr hr1]
    exact hq
  apply isCompactOperator_fractional_of_endpoint_bounds r hr hr1
    (fderiv ℂ hillHminusFourierDefect (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b))
    (fderiv ℂ (fun a : WeightedCoeff (Weight.sobolev 0) 2 =>
      hillL2NativeComplexFourierRemainder (sobolevToL2 (by norm_num) a)) q)
  · intro N a k
    have hh := fractionalFourierDefect_fderiv_rough r hr hr1 b
      (frequencyBand (Weight.sobolev (-r)) N a.val) hb k
    have he : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith)
        (frequencyBand (Weight.sobolev (-r)) N a.val) =
          frequencyBand (Weight.sobolev (-1)) N a.val := by
      apply Subtype.ext
      funext j
      simp only [sobolevInclusion_apply, frequencyBand_apply]
    rw [he] at hh
    exact hh.symm
  · intro N a k
    have hh := fractionalFourierDefect_fderiv_l2 r hr hr1 q
      (frequencyBand (Weight.sobolev 0) N a.val) hq k
    have he : sobolevInclusion (show -r ≤ 0 by linarith)
        (frequencyBand (Weight.sobolev 0) N a.val) =
          frequencyBand (Weight.sobolev (-r)) N a.val := by
      apply Subtype.ext
      funext j
      simp only [sobolevInclusion_apply, frequencyBand_apply]
    rw [he] at hh
    exact hh

theorem isCompactOperator_fractionalFourierDefect_fderiv
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : IsRealPeriodOneHminusOne (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)) :
    IsCompactOperator (fderiv ℂ (hillFractionalFourierDefect r hr hr1) q) := by
  let a : ℕ → WeightedCoeff (Weight.sobolev 0) 2 := fun N =>
    finiteBlock (Weight.sobolev 0) (Coeff.lowFrequencies N) q.val
  have he (N : ℕ) : sobolevInclusion (show -r ≤ 0 by linarith) (a N) =
      frequencyProjection (Weight.sobolev (-r)) N q := by
    apply Subtype.ext
    funext k
    simp only [sobolevInclusion_apply, a, finiteBlock_val, Coeff.mem_lowFrequencies,
      frequencyProjection_apply]
  have hreal (N : ℕ) : IsRealPeriodOneHminusOne
      (periodOneL2Inclusion (sobolevToL2 (by norm_num) (a N))) := by
    intro k
    have hqk := hq k
    simp only [sobolevInclusion_apply] at hqk
    simp only [periodOneL2Inclusion_apply, sobolevToL2_apply, a, finiteBlock_val,
      Coeff.mem_lowFrequencies, Int.natAbs_neg]
    by_cases hk : k.natAbs < N
    · simp only [if_pos hk, hqk]
    · simp only [if_neg hk, map_zero]
  have ht := (analyticAt_hillFractionalFourierDefect r hr hr1 q hq).fderiv.continuousAt.tendsto.comp
    (tendsto_frequencyProjection (Weight.sobolev (-r)) q)
  apply isCompactOperator_of_tendsto ht
  apply Eventually.of_forall
  intro N
  change IsCompactOperator (fderiv ℂ (hillFractionalFourierDefect r hr hr1)
    (frequencyProjection (Weight.sobolev (-r)) N q))
  rw [← he N]
  exact isCompactOperator_fractionalFourierDefect_at_l2 r hr hr1 (a N) (hreal N)

end NLS.KdV
