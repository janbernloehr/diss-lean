import NLS.SequenceSpaces.TameSpectralConvolution
import NLS.Fourier.LocalNLSInteraction

/-! # Tame bounds for the Fourier NLS field

For Sobolev weights the cubic field is linear in the high norm and quadratic
in the raw ℓ¹ norm. Both norms are invariant under the free phases, so the
same estimate holds uniformly in time in the interaction representation.
-/
noncomputable section
namespace NLS.Fourier

@[simp] theorem norm_toCoeff_nlsConjugate (w : SpectralWeight)
    (a : WeightedCoeff w.toWeight 1) : ‖w.toCoeff (nlsConjugate w a)‖ = ‖w.toCoeff a‖ := by
  have he : w.toCoeff (nlsConjugate w a) = star (Coeff.reflection (w.toCoeff a)) := by
    ext n
    simp [nlsConjugate_apply, Coeff.reflection_apply]
  rw [he, norm_star, Coeff.reflection.norm_map]

@[simp] theorem norm_toCoeff_nlsFreeFlow (w : SpectralWeight) (time : ℝ)
    (a : WeightedCoeff w.toWeight 1) : ‖w.toCoeff (nlsFreeFlow w.toWeight time a)‖ = ‖w.toCoeff a‖ := by
  have he : w.toCoeff (nlsFreeFlow w.toWeight time a) =
      Coeff.phaseFlow (fun n => -(2*Real.pi*(n : ℝ))^2) time (w.toCoeff a) := by
    ext n
    simp only [SpectralWeight.toCoeff_apply, nlsFreeFlow, WeightedCoeff.phaseFlow_apply,
      Coeff.phaseFlow_apply]
  rw [he, (Coeff.phaseFlow _ time).norm_map]

/-- The raw convolution norm is controlled entirely by raw coefficient norms. -/
theorem norm_toCoeff_convolution_le (w : SpectralWeight) (a b : WeightedCoeff w.toWeight 1) :
    ‖w.toCoeff (w.convolution a b)‖ ≤ ‖w.toCoeff a‖*‖w.toCoeff b‖ := by
  rw [w.toCoeff_convolution]
  exact Coeff.norm_convolution_le _ _

/-- A tame bound for the actual cubic field under an additive weight estimate. -/
theorem norm_cubicNLS_le_tame (w : SpectralWeight) (C : ℝ) (hC : 0 ≤ C)
    (hadd : ∀ n k : ℤ, w (n+k) ≤ C*(w n+w k))
    (a : WeightedCoeff w.toWeight 1) :
    ‖cubicNLS w a‖ ≤ (4*C^2+2*C)*‖a‖*‖w.toCoeff a‖^2 := by
  have hc : ‖(-2*Complex.I : ℂ)‖ = 2 := by norm_num [norm_mul]
  rw [cubicNLS, norm_smul, hc]
  calc
    _ ≤ 2*(C*(‖w.convolution a a‖*‖w.toCoeff (nlsConjugate w a)‖ +
        ‖w.toCoeff (w.convolution a a)‖*‖nlsConjugate w a‖)) := by
      gcongr
      exact w.norm_convolution_le_tame C hadd _ _
    _ = 2*(C*(‖w.convolution a a‖*‖w.toCoeff a‖ +
        ‖w.toCoeff (w.convolution a a)‖*‖a‖)) := by
      rw [norm_toCoeff_nlsConjugate, norm_nlsConjugate]
    _ ≤ 2*(C*((C*(‖a‖*‖w.toCoeff a‖ + ‖w.toCoeff a‖*‖a‖))*‖w.toCoeff a‖ +
        (‖w.toCoeff a‖*‖w.toCoeff a‖)*‖a‖)) := by
      gcongr
      · exact w.norm_convolution_le_tame C hadd _ _
      · exact norm_toCoeff_convolution_le w a a
    _ = _ := by ring

/-- Sobolev cubic control with only one high norm factor. -/
theorem norm_sobolev_cubicNLS_le (s : ℝ) (hs : 0 ≤ s)
    (a : WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1) :
    ‖cubicNLS (SpectralWeight.sobolev s hs) a‖ ≤
      (4*((2 : ℝ)^s)^2+2*(2 : ℝ)^s)*‖a‖*‖(SpectralWeight.sobolev s hs).toCoeff a‖^2 :=
  norm_cubicNLS_le_tame _ _ (by positivity) (SpectralWeight.sobolev_add_le s hs) a

/-- The tame field estimate is independent of time after removing free phases. -/
theorem norm_nlsInteraction_le_tame (w : SpectralWeight) (C : ℝ) (hC : 0 ≤ C)
    (hadd : ∀ n k : ℤ, w (n+k) ≤ C*(w n+w k))
    (time : ℝ) (a : WeightedCoeff w.toWeight 1) :
    ‖nlsInteraction w time a‖ ≤ (4*C^2+2*C)*‖a‖*‖w.toCoeff a‖^2 := by
  simpa only [nlsInteraction, norm_nlsFreeFlow, norm_toCoeff_nlsFreeFlow] using
    norm_cubicNLS_le_tame w C hC hadd (nlsFreeFlow w.toWeight time a)

/-- Tame Sobolev control of the interaction field, at arbitrary positive or negative times. -/
theorem norm_sobolev_nlsInteraction_le (s : ℝ) (hs : 0 ≤ s) (time : ℝ)
    (a : WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1) :
    ‖nlsInteraction (SpectralWeight.sobolev s hs) time a‖ ≤
      (4*((2 : ℝ)^s)^2+2*(2 : ℝ)^s)*‖a‖*‖(SpectralWeight.sobolev s hs).toCoeff a‖^2 :=
  norm_nlsInteraction_le_tame _ _ (by positivity) (SpectralWeight.sobolev_add_le s hs) time a

end NLS.Fourier
