import NLS.KdV.HillNormalizedFreeInverse
import NLS.KdV.HillHalfPhysicalMaps
import NLS.KdV.SingularHillContinuousResolvent

/-! Actual physical half-denominator factorization and resolvent difference
on the entire original source-normalized periodic L2 space. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- An actual normalized coefficient operator between the SAME physical half-maps. -/
def hillPhysicalHalfResolvent (z : ℂ) (T : Coeff 2 →L[ℂ] Coeff 2) :
    CircleL2 →L[ℂ] C(AddCircle (2:ℝ),ℂ) :=
  (hillHalfDenominatorToContinuous z).comp
    (l2Synthesis.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (T.comp (l2Synthesis.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (hillHalfDenominatorL2 z))))

/-- The exact physical factorization of the EXISTING actual native resolvent. -/
theorem singularHillContinuousResolvent_eq_half (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (hS : ‖hillHalfSandwich r q z‖ ≤ 1/2) :
    singularHillContinuousResolvent (hillHalfPotentialBase r hr1 q) z =
      hillPhysicalHalfResolvent z (hillNormalizedInverse r q z) := by
  apply ContinuousLinearMap.ext
  intro F
  change singularHillContinuousDomainInclusion (-(singularHillResolventToH1 (hillHalfPotentialBase r hr1 q) z
    (singularHillL2BaseInclusion F))) = _
  rw [singularHillResolventToH1_eq_normalized r hr hr1 q n hn hlog z hz hS]
  simp only [neg_apply,neg_neg]
  change singularHillContinuousDomainInclusion (hillHalfToH1 z
    (hillNormalizedInverse r q z (hillHalfFromBase z (singularHillL2BaseInclusion F)))) = _
  rw [hillHalfToH1_physicalContinuous n hn z hz,hillHalfFromBase_physicalL2 n hn z hz]
  rfl

/-- The actual free native resolvent has the same half-maps and exact phase inverse. -/
theorem singularHillContinuousResolvent_zero_eq_half (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (hlog : 1 < Real.log (n:ℝ)) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    singularHillContinuousResolvent 0 z = hillPhysicalHalfResolvent z (hillNormalizedPhaseInverse z) := by
  have h := singularHillContinuousResolvent_eq_half r hr hr1 0 n hn hlog z hz
    (by rw [hillHalfSandwich_zero r hr hr1 n hn hlog z hz];norm_num)
  simpa only [map_zero,hillNormalizedInverse_zero r hr hr1 n hn hlog z hz] using h

/-- The physical half-map construction retains subtraction of the actual middle operators. -/
theorem hillPhysicalHalfResolvent_sub (z : ℂ) (T U : Coeff 2 →L[ℂ] Coeff 2) :
    hillPhysicalHalfResolvent z T-hillPhysicalHalfResolvent z U = hillPhysicalHalfResolvent z (T-U) := by
  apply ContinuousLinearMap.ext
  intro F
  change hillHalfDenominatorToContinuous z (l2Synthesis (T (l2Synthesis.symm (hillHalfDenominatorL2 z F))))-
    hillHalfDenominatorToContinuous z (l2Synthesis (U (l2Synthesis.symm (hillHalfDenominatorL2 z F)))) =
    hillHalfDenominatorToContinuous z (l2Synthesis ((T-U) (l2Synthesis.symm (hillHalfDenominatorL2 z F))))
  rw [← map_sub,← map_sub]
  rfl

/-- The ACTUAL physical resolvent difference has the exact source half-factorization. -/
theorem singularHillContinuousResolvent_sub_zero_eq_half (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (hS : ‖hillHalfSandwich r q z‖ ≤ 1/2) :
    singularHillContinuousResolvent (hillHalfPotentialBase r hr1 q) z-singularHillContinuousResolvent 0 z =
      hillPhysicalHalfResolvent z (hillNormalizedInverse r q z-hillNormalizedPhaseInverse z) := by
  rw [singularHillContinuousResolvent_eq_half r hr hr1 q n hn hlog z hz hS,
    singularHillContinuousResolvent_zero_eq_half r hr hr1 n hn hlog z hz,hillPhysicalHalfResolvent_sub]

/-- The two physical Fourier isometries introduce NO extra norm constant. -/
theorem norm_hillPhysicalHalfResolvent_le (z : ℂ) (T : Coeff 2 →L[ℂ] Coeff 2) :
    ‖hillPhysicalHalfResolvent z T‖ ≤ ‖hillHalfDenominatorToContinuous z‖*‖T‖*‖hillHalfDenominatorL2 z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro F
  change ‖hillHalfDenominatorToContinuous z (l2Synthesis (T (l2Synthesis.symm (hillHalfDenominatorL2 z F))))‖ ≤ _
  calc
    _ ≤ ‖hillHalfDenominatorToContinuous z‖*‖l2Synthesis (T (l2Synthesis.symm (hillHalfDenominatorL2 z F)))‖ :=
      (hillHalfDenominatorToContinuous z).le_opNorm _
    _ = ‖hillHalfDenominatorToContinuous z‖*‖T (l2Synthesis.symm (hillHalfDenominatorL2 z F))‖ := by
      rw [LinearIsometryEquiv.norm_map]
    _ ≤ ‖hillHalfDenominatorToContinuous z‖*(‖T‖*‖l2Synthesis.symm (hillHalfDenominatorL2 z F)‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = ‖hillHalfDenominatorToContinuous z‖*(‖T‖*‖hillHalfDenominatorL2 z F‖) := by
      rw [LinearIsometryEquiv.norm_map]
    _ ≤ ‖hillHalfDenominatorToContinuous z‖*(‖T‖*(‖hillHalfDenominatorL2 z‖*‖F‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((hillHalfDenominatorL2 z).le_opNorm F) (norm_nonneg T))
        (norm_nonneg _)
    _ = _ := by ring

/-- Actual rough-potential physical resolvent difference bound, on ALL L2 inputs. -/
theorem norm_singularHillContinuousResolvent_sub_zero_le_half (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (hS : ‖hillHalfSandwich r q z‖ ≤ 1/2) :
    ‖singularHillContinuousResolvent (hillHalfPotentialBase r hr1 q) z-singularHillContinuousResolvent 0 z‖ ≤
      ‖hillHalfDenominatorToContinuous z‖*(2*‖hillHalfSandwich r q z‖)*(Real.sqrt (n:ℝ))⁻¹ := by
  rw [singularHillContinuousResolvent_sub_zero_eq_half r hr hr1 q n hn hlog z hz hS]
  exact (norm_hillPhysicalHalfResolvent_le z _).trans
    (mul_le_mul
      (mul_le_mul_of_nonneg_left (norm_hillNormalizedInverse_sub_phaseInverse_le r q n hn z hz hS) (norm_nonneg _))
      (norm_hillHalfDenominatorL2_le n hn z hz) (norm_nonneg _) (by positivity))

end NLS.KdV
