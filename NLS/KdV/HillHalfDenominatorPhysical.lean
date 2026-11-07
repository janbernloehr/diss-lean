import NLS.KdV.HillHalfDenominator
import NLS.KdV.SingularHillPhysicalL2
import NLS.Fourier.CircleContinuousLp
import NLS.SequenceSpaces.ConvolutionSandwich

/-! The actual source half-denominator on ALL physical periodic L2 data,
with the original continuous-output and L2 operator bounds. -/
noncomputable section
open Set Metric MeasureTheory
namespace NLS.KdV
open NLS.Fourier

/-- The source D_lambda^(-1/2), realized with continuous physical outputs. -/
def hillHalfDenominatorToContinuous (z : ℂ) : CircleL2 →L[ℂ] C(AddCircle (2:ℝ),ℂ) :=
  continuousSynthesisCLM.comp ((Coeff.holderMultiplier (hillHalfDenominatorSymbol z)).comp
    l2Synthesis.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Exact original raw coefficients of every continuous-output half-denominator image. -/
theorem hillHalfDenominatorToContinuous_coefficient (z : ℂ) (F : CircleL2) (k : ℤ) :
    fourierCoeff (hillHalfDenominatorToContinuous z F) k =
      l2Synthesis.symm F k * hillHalfDenominatorSymbol z k := by
  change fourierCoeff (continuousSynthesis (Coeff.holderMultiplier (hillHalfDenominatorSymbol z)
    (l2Synthesis.symm F))) k = _
  rw [fourierCoeff_continuousSynthesis,Coeff.holderMultiplier_apply]

/-- Its physical uniform-output operator norm is bounded by the ACTUAL l2 symbol norm. -/
theorem norm_hillHalfDenominatorToContinuous_le (z : ℂ) :
    ‖hillHalfDenominatorToContinuous z‖ ≤ ‖hillHalfDenominatorSymbol z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro F
  have hb := Coeff.norm_holderMultiplier_apply_le (hillHalfDenominatorSymbol z) (l2Synthesis.symm F)
  rw [LinearIsometryEquiv.norm_map] at hb
  exact (norm_continuousSynthesis_le _).trans hb

/-- The sharp logarithmic-over-index square bound, on the ENTIRE literal source circle. -/
theorem norm_sq_hillHalfDenominatorToContinuous_le_log (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    ‖hillHalfDenominatorToContinuous z‖^2 ≤ (8*Real.exp 1+2)*Real.log (n:ℝ)/(n:ℝ) :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_hillHalfDenominatorToContinuous_le z) 2).trans
    (norm_sq_hillHalfDenominatorSymbol_le_log n hn hlog z hz)

/-- The SAME source half-denominator on the full source-normalized physical L2 space. -/
def hillHalfDenominatorL2 (z : ℂ) : CircleL2 →L[ℂ] CircleL2 :=
  l2Synthesis.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Coeff.multiplierCLM (hillHalfDenominatorBoundedSymbol z)).comp
      l2Synthesis.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Its original L2 Fourier coefficients are the same literal half-denominator products. -/
theorem hillHalfDenominatorL2_coefficient (z : ℂ) (F : CircleL2) (k : ℤ) :
    fourierCoeff (hillHalfDenominatorL2 z F) k =
      hillHalfDenominatorBoundedSymbol z k * l2Synthesis.symm F k := by
  change fourierCoeff (l2Synthesis (Coeff.multiplier (hillHalfDenominatorBoundedSymbol z)
    (l2Synthesis.symm F))) k = _
  rw [fourierCoeff_l2Synthesis,Coeff.multiplier_apply]

/-- The actual physical L2 half-denominator bound has EXACT constant ONE. -/
theorem norm_hillHalfDenominatorL2_le (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    ‖hillHalfDenominatorL2 z‖ ≤ (Real.sqrt (n:ℝ))⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro F
  change ‖l2Synthesis (Coeff.multiplier (hillHalfDenominatorBoundedSymbol z)
    (l2Synthesis.symm F))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (Coeff.norm_multiplier_le _ _).trans
    (by rw [LinearIsometryEquiv.norm_map];
        exact mul_le_mul_of_nonneg_right (norm_hillHalfDenominatorBoundedSymbol_le n hn z hz) (norm_nonneg F))

/-- The continuous output and L2 output are the SAME actual physical function. -/
theorem hillHalfDenominatorToContinuous_toLp (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (F : CircleL2) :
    circleContinuousToLp 2 (hillHalfDenominatorToContinuous z F) = hillHalfDenominatorL2 z F := by
  apply fourierBasis.repr.injective
  ext k
  rw [fourierBasis_repr,fourierBasis_repr]
  change fourierCoeff (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
    (hillHalfDenominatorToContinuous z F)) k = _
  rw [fourierCoeff_toLp,hillHalfDenominatorToContinuous_coefficient,hillHalfDenominatorL2_coefficient,
    hillHalfDenominatorSymbol_apply n hn z hz,hillHalfDenominatorBoundedSymbol_apply n hn z hz,mul_comm]

end NLS.KdV
