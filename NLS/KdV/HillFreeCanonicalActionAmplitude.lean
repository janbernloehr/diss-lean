import NLS.KdV.HillFreeFilledCriticalRatio
import NLS.KdV.HillCanonicalActionAmplitude

/-! The ACTUAL native free normalized action ratio is EXACTLY one.
The proof computes its filled quotient through any valid shifted Miura
chart, then uses intrinsic ratio uniqueness across closed gaps. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped Classical
namespace NLS.KdV
namespace HillHminusMiuraGapBall

theorem freeNormalizedSourceAction_value (B : HillHminusMiuraGapBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (n : ℕ+) :
    sourceNormalizedActionComplexExtension (by norm_num) (by norm_num) (n:ℕ)
      (hillMiuraDiagonal (B.actionBall.lift 0)) =
        B.freeFrequencyMidpoint n/(4*((Real.pi:ℂ)*n)) := by
  simp only [sourceNormalizedActionComplexExtension,sourceNormalizedActionRealExtension,
    if_pos (B.freeSourceGap_zero h0 n),sourceNormalizedActionCollapsedCandidate]
  change I*sourceCriticalRootRatioExtension (by norm_num) (by norm_num) (n:ℕ)
    (hillMiuraDiagonal (B.actionBall.lift 0)) (B.freeFrequencyMidpoint n)/4=_
  rw [B.freeCriticalRootRatio_value h0 n]
  calc
    I*(-I*B.freeFrequencyMidpoint n/((Real.pi:ℂ)*n))/4 =
        -(I^2)*B.freeFrequencyMidpoint n/(4*((Real.pi:ℂ)*n)) := by ring
    _ = _ := by rw [I_sq]; ring

theorem freeHigherNormalizedSourceAction_value (B : HillHminusMiuraGapBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (n : ℕ+) :
    sourceHigherActionOneNormalized (by norm_num) (by norm_num) (n:ℕ)
      (hillMiuraDiagonal (B.actionBall.lift 0)) =
        (B.freeFrequencyMidpoint n)^2/(4*((Real.pi:ℂ)*n)) := by
  rw [sourceHigherActionOneNormalized_eq_midpoint_mul_of_gap_zero
    (by norm_num) (by norm_num) (n:ℕ) _ (B.freeSourceGap_zero h0 n),B.freeNormalizedSourceAction_value h0 n]
  change B.freeFrequencyMidpoint n*(B.freeFrequencyMidpoint n/(4*((Real.pi:ℂ)*n))) = _
  ring

theorem normalizedRatio_zero (B : HillHminusMiuraGapBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (n : ℕ+) : B.normalizedRatio n 0=1 := by
  have ht : B.freeFrequencyMidpoint n ≠ 0 := fun he =>
    (ne_of_gt (B.freeFrequencyMidpoint_pos h0 n)) (by rw [he]; rfl)
  have hn : (Real.pi:ℂ)*n ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast n.ne_zero)
  rw [normalizedRatio,B.freeHigherNormalizedSourceAction_value h0 n]
  change (16*((Real.pi:ℂ)*n))*((B.freeFrequencyMidpoint n)^2/(4*((Real.pi:ℂ)*n)))/
    (2*B.freeFrequencyMidpoint n)^2=1
  field_simp [ht,hn]
  norm_num

end HillHminusMiuraGapBall

theorem hillHminusCanonicalActionRatio_zero (n : ℕ+) : hillHminusCanonicalActionRatio n 0=1 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  by_cases hz : ∀ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a=0
  · rw [hillHminusCanonicalActionRatio,if_pos hz]
  · have hne : ∃ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a ≠ 0 := by simpa using hz
    obtain ⟨B,hB⟩ := exists_hillHminusMiuraGapBall 0 hr
    obtain ⟨U,hU,h0U,_,hR,hfactor⟩ := B.exists_local_normalizedRatio_data n 0 hB hr
    let V := U ∩ hillHminusCanonicalRatioDomain
    have hV : IsOpen V := hU.inter isOpen_hillHminusCanonicalRatioDomain
    have h0V : (0 : PeriodOneHminusOne) ∈ V := ⟨h0U,real_mem_hillHminusCanonicalRatioDomain 0 hr⟩
    have he := hillHminusCanonicalActionRatio_unique_on_open n V hV inter_subset_right
      (B.normalizedRatio n) (hR.mono inter_subset_left) hne (fun a ha => (hfactor a ha.1).2.1)
    rw [he h0V,B.normalizedRatio_zero hB n]

theorem hillHminusActionRatioSqrt_zero (n : ℕ+) : hillHminusActionRatioSqrt n 0=1 := by
  rw [hillHminusActionRatioSqrt,hillHminusCanonicalActionRatio_zero,Complex.sqrt_one]

theorem hillHminusCanonicalActionAmplitude_zero (n : ℕ+) :
    hillHminusCanonicalActionAmplitude n 0 = 1/((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ) := by
  rw [hillHminusCanonicalActionAmplitude,hillHminusActionRatioSqrt_zero]

end NLS.KdV
