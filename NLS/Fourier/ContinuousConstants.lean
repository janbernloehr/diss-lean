import NLS.Fourier.ContinuousSynthesis
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal

namespace NLS.Fourier

theorem continuousFourierCLM_const (c : ℂ) :
    continuousFourierCLM (ContinuousMap.const (AddCircle (2 : ℝ)) c)=lp.single 2 0 c := by
  have he : continuousSynthesis (lp.single 1 0 c)=ContinuousMap.const (AddCircle (2 : ℝ)) c := by
    rw [continuousSynthesis_single]
    ext x
    simp
  ext k
  rw [continuousFourierCLM_apply,← he,fourierCoeff_continuousSynthesis]
  simp only [lp.single_apply]

end NLS.Fourier
