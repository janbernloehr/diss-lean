import NLS.Fourier.PhysicalIntervalL2
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Pointwise uniqueness from interval Fourier coefficients

Continuous functions with the same interval coefficients agree everywhere
on the closed interval. No matching of the two endpoint values is assumed.
-/
noncomputable section
open Set MeasureTheory
namespace NLS.Fourier

/-- Actual Fourier coefficients determine a continuous function on its closed interval. -/
theorem eqOn_Icc_of_intervalFourierCoefficient_eq {L : ℝ} (hL : 0 < L)
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hcoeff : ∀ n : ℤ, intervalFourierCoefficient L f n = intervalFourierCoefficient L g n) :
    EqOn f g (Icc 0 L) := by
  have hfm := memLp_two_interval hf 0 L hL.le
  have hgm := memLp_two_interval hg 0 L hL.le
  have he : intervalL2Class hL f hfm = intervalL2Class hL g hgm := by
    apply fourierBasis.repr.injective
    ext n
    simpa only [fourierBasis_repr,fourierCoeff_intervalL2Class] using hcoeff n
  have hae : f =ᵐ[volume.restrict (Ioo 0 L)] g := by
    have h₁ := intervalPullback_intervalL2Class hL f hfm
    have h₂ := intervalPullback_intervalL2Class hL g hgm
    rw [he] at h₁
    exact h₁.symm.trans h₂
  have hae' : f =ᵐ[volume.restrict (Icc 0 L)] g := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Icc] using hae
  exact Measure.eqOn_Icc_of_ae_eq volume hL.ne hae' hf.continuousOn hg.continuousOn

end NLS.Fourier
