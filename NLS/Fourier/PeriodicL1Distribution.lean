import NLS.Fourier.PeriodicL1Pairing

/-! # Actual periodic distributions from L1 data

Interval integrability suffices to construct the periodic extension and prove
its normalized action on every smooth periodic test. Locally integrable input
is a special case. The distribution has the actual normalized Fourier integrals.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal SchwartzMap ContDiff
namespace NLS.Fourier
variable (L : ℝ) [Fact (0 < L)]

/-- Bounded actual Fourier coefficients of arbitrary interval L1 data. -/
def periodicL1Coefficients (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) :
    WeightedCoeff (Weight.sobolev 0) ⊤ :=
  ⟨intervalFourierCoefficient L f, by
    change Memℓp (fun n => (Weight.sobolev 0 n : ℂ) * intervalFourierCoefficient L f n) ⊤
    simp only [Weight.sobolev_zero_apply, Complex.ofReal_one, one_mul]
    refine memℓp_infty ⟨periodicL1Size L f, ?_⟩
    rintro y ⟨n, rfl⟩
    exact norm_intervalFourierCoefficient_le_L1 L f hf n⟩

@[simp] theorem periodicL1Coefficients_apply (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) (n : ℤ) :
    (periodicL1Coefficients L f hf).val n = intervalFourierCoefficient L f n := rfl

theorem norm_periodicL1Coefficients_le (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) :
    ‖periodicL1Coefficients L f hf‖ ≤ periodicL1Size L f := by
  rw [WeightedCoeff.norm_eq]
  apply lp.norm_le_of_forall_le (periodicL1Size_nonneg L f)
  intro n
  simpa only [WeightedCoeff.weightEquiv_apply, Weight.sobolev_zero_apply,
    Complex.ofReal_one, one_mul, periodicL1Coefficients_apply] using
    norm_intervalFourierCoefficient_le_L1 L f hf n

/-- The actual tempered distribution with the Fourier coefficients of the periodic extension. -/
def periodicL1Distribution (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) : 𝓢'(ℝ, ℂ) :=
  arbitraryPeriodDistributionSynthesis L Fact.out (Weight.sobolev 0)
    (Weight.hasTemperedInverse_sobolev 0) (periodicL1Coefficients L f hf)

theorem periodicL1Distribution_periodic (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) :
    IsPeriodicDistribution L (periodicL1Distribution L f hf) :=
  arbitraryPeriodDistributionSynthesis_periodic L Fact.out _ _ _

@[simp] theorem periodicL1Distribution_coefficient (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) (n : ℤ) :
    periodicL1Distribution L f hf (periodCoefficientTest L Fact.out n) = intervalFourierCoefficient L f n :=
  arbitraryPeriodDistributionSynthesis_coefficient L Fact.out _ _ _ n

/-- Section 2's normalized periodic action, with only an L1 hypothesis on the input. -/
theorem periodicL1Distribution_smooth_action (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g L) :
    periodicL1Distribution L f hf (SchwartzMap.smulLeftCLM ℂ g (periodCoefficientTest L Fact.out 0)) =
      (L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, f x*g x := by
  obtain ⟨b, hb, _⟩ := existsUnique_smooth_arbitraryPeriod_coefficients (q := 1) L Fact.out (-0) g hg hp
  rw [← periodicDistribution_sobolevBilinearPairing_arbitraryPeriod L Fact.out 0
    (periodicL1Distribution L f hf) (periodicL1Distribution_periodic L f hf)
    (periodicL1Coefficients L f hf) (fun n => (periodicL1Distribution_coefficient L f hf n).symm)
    g hg hp b hb, WeightedCoeff.sobolevBilinearPairing_apply]
  simpa only [periodicL1Coefficients_apply, hb] using tsum_periodicL1_pairing L f hf g hg hp

/-- Absolute convergence of the physical product series under precisely the L1/smooth hypotheses. -/
theorem summable_norm_periodicL1_pairing (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g L) :
    Summable (fun n : ℤ => ‖intervalFourierCoefficient L f n * intervalFourierCoefficient L g (-n)‖) := by
  obtain ⟨b, hb, _⟩ := existsUnique_smooth_arbitraryPeriod_coefficients (q := 1) L Fact.out (-0) g hg hp
  simpa only [periodicL1Coefficients_apply, hb] using
    WeightedCoeff.summable_norm_sobolevBilinearPairing 0 (periodicL1Coefficients L f hf) b

/-- Uniqueness is among actual periodic tempered distributions. -/
theorem existsUnique_periodicL1Distribution (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) :
    ∃! T : 𝓢'(ℝ, ℂ), IsPeriodicDistribution L T ∧
      (∀ n, T (periodCoefficientTest L Fact.out n) = intervalFourierCoefficient L f n) ∧
      (∀ g : ℝ → ℂ, ContDiff ℝ ∞ g → Function.Periodic g L →
        T (SchwartzMap.smulLeftCLM ℂ g (periodCoefficientTest L Fact.out 0)) =
          (L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, f x*g x) := by
  refine ⟨periodicL1Distribution L f hf,
    ⟨periodicL1Distribution_periodic L f hf, periodicL1Distribution_coefficient L f hf,
      periodicL1Distribution_smooth_action L f hf⟩, ?_⟩
  rintro T ⟨hT, hc, _⟩
  exact periodicDistribution_ext_arbitraryPeriod L Fact.out hT (periodicL1Distribution_periodic L f hf)
    (fun n => (hc n).trans (periodicL1Distribution_coefficient L f hf n).symm)

/-- Local integrability supplies the required fundamental-interval hypothesis. -/
theorem intervalIntegrable_of_locallyIntegrable (f : ℝ → ℂ) (hf : LocallyIntegrable f volume) :
    IntervalIntegrable f volume 0 L :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le (Fact.out : 0 < L).le).mpr
    (hf.integrableOn_isCompact isCompact_Icc)

/-- Section 2's construction applies in particular to locally integrable periodic functions. -/
theorem locallyIntegrable_periodic_smooth_action (f : ℝ → ℂ) (hf : LocallyIntegrable f volume)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g L) :
    periodicL1Distribution L f (intervalIntegrable_of_locallyIntegrable L f hf)
      (SchwartzMap.smulLeftCLM ℂ g (periodCoefficientTest L Fact.out 0)) =
        (L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, f x*g x :=
  periodicL1Distribution_smooth_action L f _ g hg hp

/-- The distribution depends only on the almost-everywhere class on a fundamental interval. -/
theorem periodicL1Distribution_congr_ae (f g : ℝ → ℂ)
    (hf : IntervalIntegrable f volume 0 L) (hg : IntervalIntegrable g volume 0 L)
    (hfg : f =ᵐ[volume.restrict (Ioc 0 L)] g) :
    periodicL1Distribution L f hf = periodicL1Distribution L g hg := by
  apply periodicDistribution_ext_arbitraryPeriod L Fact.out
    (periodicL1Distribution_periodic L f hf) (periodicL1Distribution_periodic L g hg)
  intro n
  simp only [periodicL1Distribution_coefficient,
    intervalFourierCoefficient_eq_fourierCoeffOn (Fact.out : 0 < L)]
  exact congrFun (fourierCoeffOn_congr_ae (Fact.out : 0 < L) hfg) n

/-- The same construction gives the sesquilinear physical action by conjugating the test. -/
theorem periodicL1Distribution_sesquilinear_action (f : ℝ → ℂ)
    (hf : IntervalIntegrable f volume 0 L) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g L) :
    periodicL1Distribution L f hf
      (SchwartzMap.smulLeftCLM ℂ (fun x => star (g x)) (periodCoefficientTest L Fact.out 0)) =
        (L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, f x*star (g x) :=
  periodicL1Distribution_smooth_action L f hf _
    (Complex.conjCLE.contDiff.comp hg) (fun x => congrArg star (hp x))

end NLS.Fourier
