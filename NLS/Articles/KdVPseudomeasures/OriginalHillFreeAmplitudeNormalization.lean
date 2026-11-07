import NLS.KdV.HillFreeCanonicalActionAmplitude

/-! Exact free normalization of the ACTUAL native action ratio and its
positive Cartesian amplitude. These remain necessary inputs to the full
Cartesian Fourier differential, which is not asserted here. -/
noncomputable section
open NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_free_action_ratio (n : ℕ+) : hillHminusCanonicalActionRatio n 0=1 :=
  hillHminusCanonicalActionRatio_zero n

theorem original_Hill_free_action_amplitude (n : ℕ+) :
    hillHminusCanonicalActionAmplitude n 0 = 1/((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ) :=
  hillHminusCanonicalActionAmplitude_zero n

theorem original_Hill_free_normalized_Miura_ratio (B : HillHminusMiuraGapBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (n : ℕ+) : B.normalizedRatio n 0=1 :=
  B.normalizedRatio_zero h0 n

end NLS.Articles.KdVPseudomeasures
