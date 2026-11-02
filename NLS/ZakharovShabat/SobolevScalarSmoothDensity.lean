import NLS.ZakharovShabat.SobolevSourceSmoothDensity

/-! # Smooth scalar profiles determine continuous Sobolev identities -/
noncomputable section
open NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

theorem eq_of_continuous_of_smooth_scalarSobolev (s : ℕ)
    {E : Type*} [TopologicalSpace E] [T2Space E]
    (F G : ScalarSobolev s → E) (hF : Continuous F) (hG : Continuous G)
    (hsmooth : ∀ (u : ScalarSobolev s) (f : ℝ → ℂ), ContDiff ℝ ∞ f → Function.Periodic f 1 →
      (∀ j, u.val j = periodOneCoefficient f j) → F u = G u) : F = G := by
  apply (WeightedCoeff.denseRange_ofFinsupp (Weight.sobolev (s : ℝ)) 2 (by simp)).equalizer hF hG
  funext a
  apply hsmooth _ (polynomial a) (contDiff_source_polynomial a) (periodic_source_polynomial a)
  intro j
  simp only [WeightedCoeff.ofFinsupp_apply,periodOneCoefficient_source_polynomial]

end NLS.ZakharovShabat
