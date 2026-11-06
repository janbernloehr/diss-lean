import NLS.KdV.HillOriginalSequenceActions
import NLS.KdV.HillConstantActionCurves
import NLS.SequenceSpaces.SingleCoordinatePhase

/-! # The entire original Hill discriminant is determined by all Hill actions -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.KdV

def hillOriginalInverseTrace (E : ℂ) (z : lp (fun _ : ℕ => ℂ) 2) : ℂ :=
  hillHminusDiscriminant
    (hillOriginalHminusSource (hillOriginalMeanZeroSpectralInverse z).val.val) E

theorem continuous_hillOriginalInverseTrace (E : ℂ) : Continuous (hillOriginalInverseTrace E) := by
  let L : hillRealMeanZeroSourceSubmodule →L[ℝ] PeriodOneHminusOne :=
    hillOriginalRealHminusInclusion.comp hillRealMeanZeroSourceSubmodule.subtypeL
  have hD : Continuous (fun a : PeriodOneHminusOne => hillHminusDiscriminant a E) :=
    continuous_iff_continuousAt.mpr (fun a => (analyticAt_hillHminusDiscriminant_source a E).continuousAt)
  exact hD.comp (L.continuous.comp continuous_hillOriginalMeanZeroSpectralInverse)

/-- One actual smooth target rotation lifts through the constructed global
physical inverse to a mean-zero original constant-action curve. -/
theorem hillOriginalInverseTrace_coordinatePhase (E : ℂ)
    (z : lp (fun _ : ℕ => ℂ) 2) (k : ℕ) (t : ℝ) :
    hillOriginalInverseTrace E (lpCoordinatePhase z k t) = hillOriginalInverseTrace E z := by
  let γ : ℝ → hillRealMeanZeroSourceSubmodule := fun s =>
    hillOriginalMeanZeroSpectralInverse (lpCoordinatePhase z k s)
  have hγ : Differentiable ℝ γ := by
    intro s
    exact (analyticOnNhd_hillOriginalMeanZeroSpectralInverse _ (mem_univ _)).differentiableAt.comp s
      ((differentiable_lpCoordinatePhase z k) s)
  have hact (n : ℕ+) (s : ℝ) :
      hillRealGapIntegral (γ s).val.val (γ s).val.property.1 (γ s).val.property.2 n 0 =
      hillRealGapIntegral (γ 0).val.val (γ 0).val.property.1 (γ 0).val.property.2 n 0 := by
    apply hillOriginalActions_eq_of_spectral_moduli (γ s) (γ 0) _ n
    intro j
    simp only [γ,hillOriginalMeanZeroRealSpectralMap_apply_inverse,
      norm_lpCoordinatePhase_apply]
  exact hillOriginalTrace_eq_on_constant_action_curve γ hγ hact t E |>.trans
    (by simp only [γ,lpCoordinatePhase_zero]; rfl)

/-- All actual original mean-zero L2 Hill actions determine the full entire
discriminant. This includes infinite action fibers and every closed gap. -/
theorem hillHminusDiscriminant_original_eq_of_actions
    (q p : hillRealMeanZeroSourceSubmodule)
    (h : ∀ n : ℕ+, hillRealGapIntegral q.val.val q.val.property.1 q.val.property.2 n 0 =
      hillRealGapIntegral p.val.val p.val.property.1 p.val.property.2 n 0) :
    hillHminusDiscriminant (hillOriginalHminusSource q.val.val) =
      hillHminusDiscriminant (hillOriginalHminusSource p.val.val) := by
  funext E
  have he := eq_of_coordinate_moduli_of_phase_invariance (p := 2) (by norm_num)
    (hillOriginalInverseTrace E) (continuous_hillOriginalInverseTrace E)
    (hillOriginalInverseTrace_coordinatePhase E)
    (hillOriginalMeanZeroRealSpectralMap p) (hillOriginalMeanZeroRealSpectralMap q)
    (fun k => (hillOriginalSpectral_moduli_eq_of_actions q p h k).symm)
  simpa only [hillOriginalInverseTrace,hillOriginalMeanZeroSpectralInverse_apply_map] using he

theorem hillL2Discriminant_original_eq_of_actions
    (q p : hillRealMeanZeroSourceSubmodule)
    (h : ∀ n : ℕ+, hillRealGapIntegral q.val.val q.val.property.1 q.val.property.2 n 0 =
      hillRealGapIntegral p.val.val p.val.property.1 p.val.property.2 n 0) :
    hillL2Discriminant (SpectralWeight.one.toCoeff q.val.val) =
      hillL2Discriminant (SpectralWeight.one.toCoeff p.val.val) := by
  funext E
  have he := congrFun (hillHminusDiscriminant_original_eq_of_actions q p h) E
  simpa only [hillHminusDiscriminant_original_source_agreement q.val.val q.val.property.1 E,
    hillHminusDiscriminant_original_source_agreement p.val.val p.val.property.1 E] using he

end NLS.KdV
