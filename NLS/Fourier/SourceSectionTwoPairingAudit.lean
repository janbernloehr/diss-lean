import NLS.Fourier.ArbitraryPeriodBilinearParseval
import NLS.Fourier.PeriodOneCoefficients
import NLS.Fourier.DistributionModulation

/-! # The missing frequency reversal in Section 2's scalar bilinear pairing

On printed page 22 the same-index sum is described as the natural extension
of distributional action. A smooth single Fourier wave gives sum one but
physical integral zero. The corrected bilinear Parseval formula reverses
one index; ordinary sesquilinear Parseval is unchanged.
-/
noncomputable section
open scoped ContDiff
namespace NLS.Fourier

/-- A single smooth period-one mode suffices to test the printed convention. -/
def sourceSectionTwoBilinearWave : ℝ → ℂ := polynomial (Finsupp.single (1 : ℤ) (1 : ℂ))

/-- The counterexample is precisely exp(2*pi*i*x). -/
theorem sourceSectionTwoBilinearWave_eq : sourceSectionTwoBilinearWave = wave 2 := by
  funext x
  simp [sourceSectionTwoBilinearWave,polynomial]

/-- The discrepancy already occurs for smooth inputs. -/
theorem sourceSectionTwoBilinearWave_smooth : ContDiff ℝ ∞ sourceSectionTwoBilinearWave := by
  rw [sourceSectionTwoBilinearWave_eq]
  exact contDiff_wave_infty 2

/-- The physical source has period one. -/
theorem sourceSectionTwoBilinearWave_periodic : Function.Periodic sourceSectionTwoBilinearWave 1 := by
  intro x
  rw [sourceSectionTwoBilinearWave_eq,wave_add_argument]
  simpa using congrArg (fun z : ℂ => wave 2 x*z) (wave_even_at_one 1)

/-- The actual normalized Fourier integrals are the single coefficient at index one. -/
theorem sourceSectionTwoBilinearWave_coefficient (n : ℤ) :
    periodOneCoefficient sourceSectionTwoBilinearWave n = Finsupp.single (1 : ℤ) (1 : ℂ) n := by
  rw [periodOneCoefficient,sourceSectionTwoBilinearWave,fourierCoeffOn_one,halfCoefficient_polynomial_even]
  ring

/-- The printed same-index scalar pairing has value one. -/
theorem sourceSectionTwo_same_index_pairing :
    (∑' n : ℤ, periodOneCoefficient sourceSectionTwoBilinearWave n *
      periodOneCoefficient sourceSectionTwoBilinearWave n) = 1 := by
  simp [sourceSectionTwoBilinearWave_coefficient,Finsupp.single_apply]

/-- The actual normalized distributional action has value zero on the same smooth test. -/
theorem sourceSectionTwo_bilinear_integral :
    (∫ x in (0 : ℝ)..1, sourceSectionTwoBilinearWave x*sourceSectionTwoBilinearWave x) = 0 := by
  have hu : Continuous sourceSectionTwoBilinearWave := continuous_polynomial _
  rw [← tsum_bilinear_unitFourierCoefficient hu hu]
  have hc (n : ℤ) : unitFourierCoefficient sourceSectionTwoBilinearWave n =
      Finsupp.single (1 : ℤ) (1 : ℂ) n := by
    rw [unitFourierCoefficient_eq_fourierCoeffOn]
    exact sourceSectionTwoBilinearWave_coefficient n
  trans ∑' (_ : ℤ), (0 : ℂ)
  · apply tsum_congr
    intro n
    rw [hc,hc]
    by_cases hn : n = 1
    · subst n
      norm_num
    · simp [Finsupp.single_apply,Ne.symm hn]
  · simp

/-- The printed same-index formula is not the physical bilinear pairing, even on smooth periodic inputs. -/
theorem sourceSectionTwo_printed_bilinear_pairing_false :
    ¬∀ f g : ℝ → ℂ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      Function.Periodic f 1 → Function.Periodic g 1 →
      (∑' n : ℤ, periodOneCoefficient f n*periodOneCoefficient g n) =
        ∫ x in (0 : ℝ)..1, f x*g x := by
  intro h
  have he := h sourceSectionTwoBilinearWave sourceSectionTwoBilinearWave
    sourceSectionTwoBilinearWave_smooth sourceSectionTwoBilinearWave_smooth
    sourceSectionTwoBilinearWave_periodic sourceSectionTwoBilinearWave_periodic
  rw [sourceSectionTwo_same_index_pairing,sourceSectionTwo_bilinear_integral] at he
  exact one_ne_zero he

end NLS.Fourier
