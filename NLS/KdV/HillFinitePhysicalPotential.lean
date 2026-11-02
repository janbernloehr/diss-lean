import NLS.KdV.HillSmoothQuadraticTrace
import NLS.KdV.HillCanonicalGapBounds
import NLS.Fourier.FinitePeriodOneRealization
import NLS.Fourier.DistributionModulation
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Smooth physical realization of finite native Hill coefficients

Finite native period-one coefficients synthesize a smooth period-one
physical circle potential. Conjugate symmetry gives physical reality,
its zero coefficient is its mean, and Parseval gives the exact unit-period
L2 normalization. The actual Hill coefficient equals its native embedding.
-/

noncomputable section
open Set Complex Filter Topology MeasureTheory
open scoped ComplexConjugate ContDiff
namespace NLS.KdV

def hillFinitePhysicalPotential (a : ℤ →₀ ℂ) : C(AddCircle (2 : ℝ), ℂ) :=
  Fourier.continuousSynthesis (Coeff.periodDouble (Coeff.ofFinsupp (p := 1) a))

theorem hillFinitePhysicalPotential_coe (a : ℤ →₀ ℂ) :
    (fun x : ℝ => hillFinitePhysicalPotential a (x : AddCircle (2 : ℝ))) =
      Fourier.polynomial a :=
  Fourier.periodOneSynthesis_ofFinsupp a

theorem contDiff_hillFinitePhysicalPotential (a : ℤ →₀ ℂ) :
    ContDiff ℝ ∞ (fun x : ℝ => hillFinitePhysicalPotential a (x : AddCircle (2 : ℝ))) := by
  rw [hillFinitePhysicalPotential_coe]
  unfold Fourier.polynomial Finsupp.sum
  exact ContDiff.sum (fun n _ => contDiff_const.mul (Fourier.contDiff_wave_infty (2*n)))

theorem periodic_hillFinitePhysicalPotential (a : ℤ →₀ ℂ) :
    Function.Periodic (fun x : ℝ => hillFinitePhysicalPotential a (x : AddCircle (2 : ℝ))) 1 :=
  Fourier.periodOneSynthesis_periodic (Coeff.ofFinsupp (p := 1) a)

theorem real_hillFinitePhysicalPotential (a : ℤ →₀ ℂ)
    (ha : ∀ n : ℤ, a (-n) = conj (a n)) :
    ∀ x : AddCircle (2 : ℝ), (hillFinitePhysicalPotential a x).im = 0 := by
  intro x
  refine Quotient.inductionOn x ?_
  intro t
  change (hillFinitePhysicalPotential a (t : AddCircle (2 : ℝ))).im = 0
  have he := congrFun (hillFinitePhysicalPotential_coe a) t
  rw [he]
  have hc := Fourier.polynomial_conj_of_coefficients a a (fun n => by
    simpa only [neg_neg] using ha (-n)) t
  have hi := congrArg Complex.im hc
  simp only [conj_im] at hi
  linarith

theorem mean_hillFinitePhysicalPotential (a : ℤ →₀ ℂ) :
    (∫ x in (0 : ℝ)..1, hillFinitePhysicalPotential a (x : AddCircle (2 : ℝ))) = a 0 := by
  have h := Fourier.periodOneCoefficient_synthesis (Coeff.ofFinsupp (p := 1) a) 0
  unfold Fourier.periodOneCoefficient at h
  rw [fourierCoeffOn_eq_integral] at h
  simpa [Fourier.periodOneSynthesis, hillFinitePhysicalPotential] using h

theorem hillContinuousCoefficients_finitePhysical (a : ℤ →₀ ℂ) :
    hillContinuousCoefficients (hillFinitePhysicalPotential a) =
      hillPeriodOneUnitPotential SpectralWeight.one
        (WeightedCoeff.ofFinsupp SpectralWeight.one.doubleIndex.toWeight 2 a) := by
  apply Subtype.ext
  funext k
  rw [hillContinuousCoefficients_apply]
  change fourierCoeff (Fourier.continuousSynthesis
    (Coeff.periodDouble (Coeff.ofFinsupp (p := 1) a))) k = _
  rw [Fourier.fourierCoeff_continuousSynthesis]
  change Coeff.periodDouble (Coeff.ofFinsupp (p := 1) a) k =
    (hillForgetWeight SpectralWeight.one 2 (hillPeriodOnePotential SpectralWeight.one
      (WeightedCoeff.ofFinsupp SpectralWeight.one.doubleIndex.toWeight 2 a))).val k
  rw [hillForgetWeight_apply]
  by_cases hk : k % 2 = 0
  · have he : k = 2 * (k/2) := by omega
    rw [he, Coeff.periodDouble_even, hillPeriodOnePotential_even]
    rfl
  · have he : k = 2 * (k/2) + 1 := by omega
    rw [he, Coeff.periodDouble_odd, hillPeriodOnePotential_odd]

theorem norm_sq_hillFiniteNative (a : ℤ →₀ ℂ) :
    ‖WeightedCoeff.ofFinsupp SpectralWeight.one.doubleIndex.toWeight 2 a‖^2 =
      ∑ n ∈ a.support, ‖a n‖^2 := by
  have he : WeightedCoeff.weightEquiv SpectralWeight.one.doubleIndex.toWeight 2
      (WeightedCoeff.ofFinsupp SpectralWeight.one.doubleIndex.toWeight 2 a) =
        Coeff.ofFinsupp (p := 2) a := by
    ext k
    simp only [WeightedCoeff.weightEquiv_apply, WeightedCoeff.ofFinsupp_apply,
      SpectralWeight.doubleIndex_apply, SpectralWeight.one_apply,
      ofReal_one, one_mul, Coeff.ofFinsupp_apply]
  rw [WeightedCoeff.norm_eq, he, Coeff.norm_ofFinsupp_sq]


end NLS.KdV
