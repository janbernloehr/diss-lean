import NLS.SequenceSpaces.Compact
import NLS.SequenceSpaces.FourierTail
import NLS.SequenceSpaces.Weighted
import Mathlib.Analysis.SpecificLimits.Basic

/-! Compact Fourier heads in weighted Hilbert spaces, including their
strong convergence along the dyadic cutoffs. -/
noncomputable section
open Filter
namespace NLS.FunctionalAnalysis
theorem isCompactOperator_conjugate {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) (S : F →L[ℂ] E) (K : F →L[ℂ] F)
    (hK : IsCompactOperator K) : IsCompactOperator (S.comp (K.comp T)) :=
  (hK.comp_clm T).clm_comp S
end NLS.FunctionalAnalysis
namespace NLS.WeightedCoeff

def frequencyProjection (w : Weight) (N : ℕ) : WeightedCoeff w 2 →L[ℂ] WeightedCoeff w 2 :=
  ((weightIsometry w 2).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((Coeff.truncateCLM (Coeff.lowFrequencies N)).comp
      (weightIsometry w 2).toContinuousLinearEquiv.toContinuousLinearMap)

theorem frequencyProjection_apply (w : Weight) (N : ℕ) (a : WeightedCoeff w 2) (k : ℤ) :
    (frequencyProjection w N a).val k = if k.natAbs < N then a.val k else 0 := by
  change (truncate w 2 (Coeff.lowFrequencies N) a).val k = _
  simp only [truncate_apply, Coeff.mem_lowFrequencies]

theorem isCompactOperator_frequencyProjection (w : Weight) (N : ℕ) :
    IsCompactOperator (frequencyProjection w N) :=
  NLS.FunctionalAnalysis.isCompactOperator_conjugate _ _ _
    (Coeff.isCompactOperator_truncateCLM (Coeff.lowFrequencies N))

theorem tendsto_frequencyProjection (w : Weight) (a : WeightedCoeff w 2) :
    Tendsto (fun N => frequencyProjection w N a) atTop (nhds a) := by
  have h := (tendsto_const_nhds (x := weightEquiv w 2 a)).sub
    (Coeff.tendsto_fourierTail (by norm_num) (weightEquiv w 2 a))
  simp only [Coeff.fourierTail, sub_sub_cancel, sub_zero] at h
  have hh := ((weightIsometry w 2).symm.continuous.tendsto (weightEquiv w 2 a)).comp h
  change Tendsto (fun N => frequencyProjection w N a) atTop
    (nhds ((weightIsometry w 2).symm ((weightIsometry w 2) a))) at hh
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hh

theorem tendsto_dyadicFrequencyProjection (w : Weight) (a : WeightedCoeff w 2) :
    Tendsto (fun j : ℕ => frequencyProjection w (2^j) a) atTop (nhds a) :=
  (tendsto_frequencyProjection w a).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2:ℕ)))

end NLS.WeightedCoeff
