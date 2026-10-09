import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.ZakharovShabat.SobolevPhysicalJets
import NLS.Fourier.FinitePeriodOneRealization
import NLS.Fourier.DistributionModulation

/-! # Smooth complex periodic sources determine continuous Sobolev maps -/
noncomputable section
open Set NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Finite source coefficients in any original integer Sobolev space. -/
def sobolevSourceOfFinsupp (s : ℕ) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) : SobolevSource s :=
  (WeightedCoeff.ofFinsupp _ 2 a.1,WeightedCoeff.ofFinsupp _ 2 a.2)

theorem denseRange_sobolevSourceOfFinsupp (s : ℕ) : DenseRange (sobolevSourceOfFinsupp s) :=
  (WeightedCoeff.denseRange_ofFinsupp _ 2 (by simp)).prodMap
    (WeightedCoeff.denseRange_ofFinsupp _ 2 (by simp))

theorem contDiff_source_polynomial (a : ℤ →₀ ℂ) : ContDiff ℝ ∞ (polynomial a) := by
  unfold polynomial Finsupp.sum
  fun_prop

theorem periodic_source_polynomial (a : ℤ →₀ ℂ) : Function.Periodic (polynomial a) 1 := by
  rw [← periodOneSynthesis_ofFinsupp]
  exact periodOneSynthesis_periodic _

@[simp] theorem periodOneCoefficient_source_polynomial (a : ℤ →₀ ℂ) (j : ℤ) :
    periodOneCoefficient (polynomial a) j = a j := by
  rw [← periodOneSynthesis_ofFinsupp,periodOneCoefficient_synthesis]
  rfl

/-- Equality on smooth complex period-one inputs determines a continuous identity on the whole Hˢ space. -/
theorem eq_of_continuous_of_smooth_sobolevSource
    (s : ℕ) {E : Type*} [TopologicalSpace E] [T2Space E]
    (F G : SobolevSource s → E) (hF : Continuous F) (hG : Continuous G)
    (hsmooth : ∀ (ab : SobolevSource s) (f g : ℝ → ℂ),
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → Function.Periodic f 1 → Function.Periodic g 1 →
      (∀ j, ab.1.val j = periodOneCoefficient f j) →
      (∀ j, ab.2.val j = periodOneCoefficient g j) → F ab = G ab) : F = G := by
  apply (denseRange_sobolevSourceOfFinsupp s).equalizer hF hG
  funext a
  apply hsmooth (sobolevSourceOfFinsupp s a) (polynomial a.1) (polynomial a.2)
    (contDiff_source_polynomial _) (contDiff_source_polynomial _)
    (periodic_source_polynomial _) (periodic_source_polynomial _)
  · intro j
    simp [sobolevSourceOfFinsupp]
  · intro j
    simp [sobolevSourceOfFinsupp]

end NLS.ZakharovShabat
