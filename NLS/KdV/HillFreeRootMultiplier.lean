import NLS.KdV.HillFreeMiuraTraceCurvature
import NLS.KdV.HillFreeFilledCriticalRatio
import NLS.ZakharovShabat.SourceCollapsedRootMultiplier

/-! Exact ACTUAL free deleted root multiplier, with its branch sign,
for every positive original index and every valid shifted Miura gap ball. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV.HillHminusMiuraGapBall

theorem freeRootMultiplier_value (B : HillHminusMiuraGapBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (n : ℕ+) :
    sourceGapRootMultiplier (by norm_num) (by norm_num) (n:ℕ)
      (hillMiuraDiagonal (B.actionBall.lift 0)) (B.freeFrequencyMidpoint n) =
        2*I*(-1:ℂ)^(n:ℕ)*B.freeFrequencyMidpoint n/((Real.pi:ℂ)*n) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hreal := B.actionBall.diracSource_real 0 h0 hr
  have ht : B.freeFrequencyMidpoint n ≠ 0 := fun he =>
    (ne_of_gt (B.freeFrequencyMidpoint_pos h0 n)) (by rw [he]; rfl)
  have hs : (Real.pi:ℂ)*n ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast n.ne_zero)
  have hc := sourceGapRootMultiplier_collapsed_curvature (by norm_num) (by norm_num) (n:ℕ)
    (hillMiuraDiagonal (B.actionBall.lift 0)) hreal (B.freeSourceGap_zero h0 n)
  change deriv (deriv (canonicalDiscriminant (by norm_num)
    (periodOnePotential (hillMiuraDiagonal (B.actionBall.lift 0))))) (B.freeFrequencyMidpoint n) = _ at hc
  rw [(B.hasDerivAt_free_trace_deriv h0 n).deriv] at hc
  change -2*(-1:ℂ)^(n:ℕ)*(B.freeFrequencyMidpoint n)^2/((Real.pi:ℂ)*n)^2 =
    -sourceCriticalRootRatioExtension (by norm_num) (by norm_num) (n:ℕ)
      (hillMiuraDiagonal (B.actionBall.lift 0)) (B.freeFrequencyMidpoint n)*
        sourceGapRootMultiplier (by norm_num) (by norm_num) (n:ℕ)
          (hillMiuraDiagonal (B.actionBall.lift 0)) (B.freeFrequencyMidpoint n) at hc
  rw [B.freeCriticalRootRatio_value h0 n] at hc
  have hbal : (I*B.freeFrequencyMidpoint n/((Real.pi:ℂ)*n))*
      sourceGapRootMultiplier (by norm_num) (by norm_num) (n:ℕ)
        (hillMiuraDiagonal (B.actionBall.lift 0)) (B.freeFrequencyMidpoint n) =
      -2*(-1:ℂ)^(n:ℕ)*(B.freeFrequencyMidpoint n)^2/((Real.pi:ℂ)*n)^2 := by
    simpa only [neg_div,neg_mul,neg_neg] using hc.symm
  apply mul_left_cancel₀ (div_ne_zero (mul_ne_zero I_ne_zero ht) hs)
  rw [hbal]
  field_simp [hs]
  simp only [I_sq]

theorem freeOmittedRootProduct_value (B : HillHminusMiuraGapBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (n : ℕ+) :
    sourceStandardRootOmittedProduct (by norm_num) (by norm_num) (n:ℕ)
      (hillMiuraDiagonal (B.actionBall.lift 0)) (B.freeFrequencyMidpoint n) =
        (-1:ℂ)^(n:ℕ)*B.freeFrequencyMidpoint n/((Real.pi:ℂ)*n) := by
  apply mul_left_cancel₀ (show (2:ℂ)*I ≠ 0 by simp)
  calc
    _ = 2*I*(-1:ℂ)^(n:ℕ)*B.freeFrequencyMidpoint n/((Real.pi:ℂ)*n) :=
      B.freeRootMultiplier_value h0 n
    _ = _ := by ring

end NLS.KdV.HillHminusMiuraGapBall
