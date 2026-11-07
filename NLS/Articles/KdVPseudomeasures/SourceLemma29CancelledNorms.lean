import NLS.SequenceSpaces.TwoSymmetricInfinityModes
import NLS.KdV.PseudomeasureWeightedCoefficients
import NLS.Fourier.PeriodicEqualWeightIsometry

/-! Exact cancelling-weight norms relevant to the literal unweighted
right-hand factor in Lemma 2.9(i). No counterexample is asserted here. -/
noncomputable section
open scoped ENNReal
open NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem sobolev_negative_weight_cancels (r : ℝ) (hr : 0 ≤ r) :
    (SpectralWeight.sobolev r hr).negativeSobolev r = Weight.one := by
  apply Weight.eq_of_values
  intro k
  rw [SpectralWeight.negativeSobolev_apply,SpectralWeight.sobolev_apply]
  exact div_self ((Weight.sobolev r).positive k).ne'

theorem norm_twoModes_cancelling_weight (r : ℝ) (hr : 0 ≤ r) (m : ℤ) (hm : m ≠ 0) :
    ‖twoSymmetricInfinityModes ((SpectralWeight.sobolev r hr).negativeSobolev r) m‖ = 1 := by
  rw [norm_twoSymmetricInfinityModes _ ((SpectralWeight.sobolev r hr).negativeSobolev_neg r) m hm]
  rw [sobolev_negative_weight_cancels]
  rfl

theorem endpointForgetWeight_twoSymmetricInfinityModes (w : SpectralWeight) (r : ℝ) (m : ℤ) :
    endpointForgetWeight w r (twoSymmetricInfinityModes (w.negativeSobolev r) m) =
      twoSymmetricInfinityModes (SpectralWeight.one.negativeSobolev r) m := by
  apply Subtype.ext
  funext k
  simp only [endpointForgetWeight_apply,twoSymmetricInfinityModes_apply]

theorem norm_twoModes_unweighted_negative (r : ℝ) (hr : 0 ≤ r) (m : ℤ) (hm : m ≠ 0) :
    ‖endpointForgetWeight (SpectralWeight.sobolev r hr) r
      (twoSymmetricInfinityModes ((SpectralWeight.sobolev r hr).negativeSobolev r) m)‖ =
        1/Weight.sobolev r m := by
  rw [endpointForgetWeight_twoSymmetricInfinityModes,
    norm_twoSymmetricInfinityModes _ (SpectralWeight.one.negativeSobolev_neg r) m hm]
  simp only [SpectralWeight.negativeSobolev_apply,SpectralWeight.one_apply]

end NLS.Articles.KdVPseudomeasures
