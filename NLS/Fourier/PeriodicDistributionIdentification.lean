import NLS.Fourier.PeriodicDistributionKernel

/-!
# Fourier identification of arbitrary periodic tempered distributions

Periodicity alone gives reconstruction from the existing coefficient-extracting
Schwartz tests. The Banach `lp` condition on these coefficients is therefore
necessary and sufficient for unique representation by distributional synthesis.
-/

noncomputable section
open scoped ENNReal SchwartzMap FourierTransform ContDiff
namespace NLS.Fourier

/-- A modulated zero-mode window has the same periodization as the corresponding coefficient test. -/
theorem periodization_wave_window (k : ℤ) :
    periodizationCLM (SchwartzMap.smulLeftCLM ℂ (wave k) (coefficientTest 0)) =
      periodizationCLM (coefficientTest (-k)) := by
  classical
  apply continuousFourierCLM_injective
  ext n
  simp only [continuousFourierCLM_apply, fourierCoeff_periodization]
  have hn : (n : ℝ) / 2 = -((-n : ℤ) : ℝ) / 2 := by simp
  rw [hn, fourier_sample_wave_mul]
  simp only [coefficientTest, FourierTransform.fourier_fourierInv_eq, frequencyTest_sample]
  have he : -n + k = 0 ↔ -n = -k := by omega
  simp only [he]

/-- For any periodic distribution, modulated windows read the existing signed coefficients. -/
theorem IsPeriodTwoDistribution.wave_window {T : 𝓢'(ℝ, ℂ)} (hT : IsPeriodTwoDistribution T)
    (k : ℤ) :
    T (SchwartzMap.smulLeftCLM ℂ (wave k) (coefficientTest 0)) = T (coefficientTest (-k)) :=
  hT.eq_of_periodization_eq (periodization_wave_window k)

/-- Every periodic tempered distribution is reconstructed by its coefficient-test values. -/
theorem IsPeriodTwoDistribution.fourier_reconstruction {T : 𝓢'(ℝ, ℂ)}
    (hT : IsPeriodTwoDistribution T) (g : 𝓢(ℝ, ℂ)) :
    T g = ∑' n : ℤ, T (coefficientTest n) * (𝓕 g) (-(n : ℝ) / 2) := by
  rw [hT.window_reconstruction g, distribution_windowed_fourier_eq_tsum]
  simp_rw [hT.wave_window, fourierCoeff_periodization]
  rw [← tsum_mul_left]
  calc
    _ = ∑' n : ℤ, T (coefficientTest (-n)) * (𝓕 g) ((n : ℝ) / 2) := by
      apply tsum_congr
      intro n
      ring
    _ = _ := by
      have h := (Equiv.neg ℤ).tsum_eq
        (fun n : ℤ => T (coefficientTest n) * (𝓕 g) (-(n : ℝ) / 2))
      change (∑' n : ℤ, T (coefficientTest (-n)) * (𝓕 g) (-((-n : ℤ) : ℝ) / 2)) = _ at h
      simpa only [Int.cast_neg, neg_neg] using h

/-- The reconstruction series is absolutely convergent, with no coefficient-space hypothesis. -/
theorem IsPeriodTwoDistribution.summable_norm_fourier_reconstruction {T : 𝓢'(ℝ, ℂ)}
    (hT : IsPeriodTwoDistribution T) (g : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖T (coefficientTest n) * (𝓕 g) (-(n : ℝ) / 2)‖) := by
  have h := (summable_norm_distribution_windowed_fourier T g (coefficientTest 0)).mul_left 2
  simp_rw [hT.wave_window, fourierCoeff_periodization] at h
  have he (n : ℤ) : 2 * ‖(1 / 2 : ℂ) * (𝓕 g) ((n : ℝ) / 2) * T (coefficientTest (-n))‖ =
      ‖T (coefficientTest (-n)) * (𝓕 g) ((n : ℝ) / 2)‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    norm_num
    ring
  simp_rw [he] at h
  have h' := h.comp_injective (neg_injective (G := ℤ))
  simpa only [Function.comp_def, neg_neg, Int.cast_neg] using h'

/-- Fourier coefficient-test values determine every periodic tempered distribution uniquely. -/
theorem periodicDistribution_ext {T U : 𝓢'(ℝ, ℂ)}
    (hT : IsPeriodTwoDistribution T) (hU : IsPeriodTwoDistribution U)
    (h : ∀ n : ℤ, T (coefficientTest n) = U (coefficientTest n)) : T = U := by
  ext g
  rw [hT.fourier_reconstruction g, hU.fourier_reconstruction g]
  exact tsum_congr (fun n => by rw [h n])

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The synthesized distributions satisfy the intrinsic periodicity predicate. -/
theorem isPeriodTwoDistribution_distributionSynthesis (a : Coeff p) :
    IsPeriodTwoDistribution (distributionSynthesis a) :=
  distributionSynthesis_period_two a

/-- Prescribed Banach Fourier coefficients reconstruct an arbitrary periodic distribution. -/
theorem distributionSynthesis_eq_of_periodic_coefficients {T : 𝓢'(ℝ, ℂ)}
    (hT : IsPeriodTwoDistribution T) (a : Coeff p)
    (ha : ∀ n : ℤ, a n = T (coefficientTest n)) : distributionSynthesis a = T := by
  apply periodicDistribution_ext (isPeriodTwoDistribution_distributionSynthesis a) hT
  intro n
  simpa only [distributionSynthesis_coefficientTest] using ha n

/-- Exact intrinsic characterization of the realized Fourier class, including the infinity endpoint. -/
theorem periodicDistribution_memlp_iff_existsUnique (T : 𝓢'(ℝ, ℂ)) :
    (IsPeriodTwoDistribution T ∧ Memℓp (fun n : ℤ => T (coefficientTest n)) p) ↔
      ∃! a : Coeff p, distributionSynthesis a = T := by
  constructor
  · rintro ⟨hT, ha⟩
    let a : Coeff p := ⟨fun n => T (coefficientTest n), ha⟩
    have he : distributionSynthesis a = T :=
      distributionSynthesis_eq_of_periodic_coefficients hT a (fun _ => rfl)
    refine ⟨a, he, fun b hb => ?_⟩
    exact distributionSynthesis_injective (hb.trans he.symm)
  · rintro ⟨a, ha, _⟩
    rw [← ha]
    refine ⟨isPeriodTwoDistribution_distributionSynthesis a, ?_⟩
    simpa only [distributionSynthesis_coefficientTest] using lp.memℓp a

end NLS.Fourier
