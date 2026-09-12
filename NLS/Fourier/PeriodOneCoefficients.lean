import NLS.SequenceSpaces.PeriodDoubling
import NLS.Fourier.ContinuousSynthesis

/-!
# Actual Fourier integrals for period-one functions

Repeating a period-one function on the period-two interval preserves its
coefficients at even indices and annihilates the odd ones. The proof splits
and translates the actual integrals; interval integrability suffices, so jumps
are allowed. Absolutely summable coefficients also give a continuous
period-one realization through the even embedding.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Period-one Fourier coefficients use the normalized unit-circle convention. -/
def periodOneCoefficient (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n

/-- Fourier waves multiply under addition of the physical argument. -/
theorem wave_add_argument (n : ℤ) (x y : ℝ) : wave n (x + y) = wave n x * wave n y := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A period-one integrable function has the expected two-half coefficient formula. -/
theorem periodTwoCoefficient_of_periodic (f : ℝ → ℂ) (hper : Function.Periodic f 1)
    (hf : IntervalIntegrable f volume 0 1) (n : ℤ) :
    periodTwoCoefficient f n = (1 + wave (-n) 1) * halfCoefficient f n := by
  have hf1 : IntervalIntegrable f volume 1 2 := by
    have he : (fun x : ℝ => f (x + -1)) = f := by
      funext x
      have hx := (hper (x - 1)).symm
      simpa [sub_eq_add_neg] using hx
    simpa only [he, sub_neg_eq_add, zero_add, one_add_one_eq_two] using hf.comp_add_right (-1)
  let g := fun x : ℝ => f x * wave (-n) x
  have hg0 : IntervalIntegrable g volume 0 1 := hf.mul_continuousOn (continuous_wave _).continuousOn
  have hg1 : IntervalIntegrable g volume 1 2 := hf1.mul_continuousOn (continuous_wave _).continuousOn
  have hshift (x : ℝ) : g (x + 1) = wave (-n) 1 * g x := by
    dsimp only [g]
    rw [hper x, wave_add_argument]
    ring
  have hsecond : (∫ x in (1 : ℝ)..2, g x) = wave (-n) 1 * ∫ x in (0 : ℝ)..1, g x := by
    calc
      _ = ∫ x in (0 : ℝ)..1, g (x + 1) := by
        simpa only [zero_add, one_add_one_eq_two] using
          (intervalIntegral.integral_comp_add_right (a := 0) (b := 1) g 1).symm
      _ = ∫ x in (0 : ℝ)..1, wave (-n) 1 * g x := by simp only [hshift]
      _ = _ := intervalIntegral.integral_const_mul _ _
  change (1 / 2 : ℂ) * (∫ x in (0 : ℝ)..2, g x) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hg0 hg1, hsecond]
  change _ = (1 + wave (-n) 1) * ((1 / 2 : ℂ) * ∫ x in (0 : ℝ)..1, g x)
  ring

/-- Even period-two coefficients equal the actual period-one coefficients, with no factor two lost. -/
theorem periodTwoCoefficient_periodic_even (f : ℝ → ℂ) (hper : Function.Periodic f 1)
    (hf : IntervalIntegrable f volume 0 1) (n : ℤ) :
    periodTwoCoefficient f (2 * n) = periodOneCoefficient f n := by
  rw [periodTwoCoefficient_of_periodic f hper hf, show -(2 * n) = 2 * (-n) by ring,
    wave_even_at_one]
  simpa only [periodOneCoefficient, one_add_one_eq_two] using (fourierCoeffOn_one f n).symm

/-- Every odd Fourier integral vanishes for period-one data, including negative odd indices. -/
theorem periodTwoCoefficient_periodic_odd (f : ℝ → ℂ) (hper : Function.Periodic f 1)
    (hf : IntervalIntegrable f volume 0 1) (n : ℤ) :
    periodTwoCoefficient f (2 * n + 1) = 0 := by
  rw [periodTwoCoefficient_of_periodic f hper hf,
    show -(2 * n + 1) = 2 * (-n - 1) + 1 by ring, wave_odd_at_one]
  ring

/-- Any integrable period-one function with `lp` coefficients embeds by even insertion. -/
theorem periodTwoCoefficient_eq_periodDouble {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : ℝ → ℂ) (hper : Function.Periodic f 1) (hf : IntervalIntegrable f volume 0 1)
    (a : Coeff p) (ha : ∀ n : ℤ, periodOneCoefficient f n = a n) :
    periodTwoCoefficient f = fun n => Coeff.periodDouble a n := by
  funext n
  by_cases hn : n % 2 = 0
  · have he : n = 2 * (n / 2) := by omega
    rw [he, periodTwoCoefficient_periodic_even f hper hf, Coeff.periodDouble_even, ha]
  · have he : n = 2 * (n / 2) + 1 := by omega
    rw [he, periodTwoCoefficient_periodic_odd f hper hf, Coeff.periodDouble_odd]

/-- Physical period doubling retains membership in every coefficient exponent. -/
theorem memlp_periodTwoCoefficient_of_periodic {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : ℝ → ℂ) (hper : Function.Periodic f 1) (hf : IntervalIntegrable f volume 0 1)
    (a : Coeff p) (ha : ∀ n : ℤ, periodOneCoefficient f n = a n) :
    Memℓp (periodTwoCoefficient f) p := by
  rw [periodTwoCoefficient_eq_periodDouble f hper hf a ha]
  exact lp.memℓp (Coeff.periodDouble a)

/-- The norm of the actual period-two integral sequence equals the original coefficient norm. -/
theorem norm_periodTwoCoefficient_of_periodic {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : ℝ → ℂ) (hper : Function.Periodic f 1) (hf : IntervalIntegrable f volume 0 1)
    (a : Coeff p) (ha : ∀ n : ℤ, periodOneCoefficient f n = a n) :
    ‖(⟨periodTwoCoefficient f, memlp_periodTwoCoefficient_of_periodic f hper hf a ha⟩ : Coeff p)‖ = ‖a‖ := by
  have he : (⟨periodTwoCoefficient f, memlp_periodTwoCoefficient_of_periodic f hper hf a ha⟩ : Coeff p) =
      Coeff.periodDouble a := by
    apply lp.ext
    exact periodTwoCoefficient_eq_periodDouble f hper hf a ha
  rw [he, Coeff.norm_periodDouble]

/-- The continuous physical function obtained by embedding period-one coefficients into period two. -/
def periodOneSynthesis (a : Coeff 1) (x : ℝ) : ℂ :=
  continuousSynthesis (Coeff.periodDouble a) (x : AddCircle (2 : ℝ))

/-- Its real-line Fourier series uses the correct period-one waves `exp(2πinx)`. -/
theorem periodOneSynthesis_eq_tsum (a : Coeff 1) (x : ℝ) :
    periodOneSynthesis a x = ∑' n : ℤ, a n * wave (2 * n) x := by
  rw [periodOneSynthesis, continuousSynthesis_apply]
  have he := (Coeff.parityEmbedding 0).injective.tsum_eq
    (f := fun k : ℤ => Coeff.periodDouble a k * wave k x) (by
      intro k hk
      by_contra hout
      have hz := Coeff.insert_apply_outside (Coeff.parityEmbedding 0) a k hout
      exact hk (by change Coeff.insert (Coeff.parityEmbedding 0) a k * _ = 0; rw [hz, zero_mul]))
  simpa only [Coeff.parityEmbedding_apply, add_zero, Coeff.periodDouble_even] using he.symm

/-- The synthesized function is actually period one, as an equality at every real argument. -/
theorem periodOneSynthesis_periodic (a : Coeff 1) : Function.Periodic (periodOneSynthesis a) 1 := by
  intro x
  simp only [periodOneSynthesis_eq_tsum, wave_add_argument, wave_even_at_one, mul_one]

/-- Absolute coefficient summability supplies a continuous physical period-one function. -/
theorem continuous_periodOneSynthesis (a : Coeff 1) : Continuous (periodOneSynthesis a) :=
  (continuousSynthesis (Coeff.periodDouble a)).continuous.comp (by fun_prop)

/-- Taking the actual unit-interval Fourier integral recovers every input coefficient. -/
@[simp] theorem periodOneCoefficient_synthesis (a : Coeff 1) (n : ℤ) :
    periodOneCoefficient (periodOneSynthesis a) n = a n := by
  rw [← periodTwoCoefficient_periodic_even _ (periodOneSynthesis_periodic a)
    ((continuous_periodOneSynthesis a).intervalIntegrable 0 1)]
  change periodTwoCoefficient (fun x : ℝ => continuousSynthesis (Coeff.periodDouble a)
    (x : AddCircle (2 : ℝ))) (2 * n) = a n
  rw [periodTwoCoefficient_circle, fourierCoeff_continuousSynthesis, Coeff.periodDouble_even]

/-- The full period-two integral sequence of the realized function is exactly the even insertion. -/
@[simp] theorem periodTwoCoefficient_periodOneSynthesis (a : Coeff 1) (n : ℤ) :
    periodTwoCoefficient (periodOneSynthesis a) n = Coeff.periodDouble a n :=
  congrFun (periodTwoCoefficient_eq_periodDouble _ (periodOneSynthesis_periodic a)
    ((continuous_periodOneSynthesis a).intervalIntegrable 0 1) a (periodOneCoefficient_synthesis a)) n

/-- The physical period-one realization loses no absolutely summable coefficient data. -/
theorem periodOneSynthesis_injective : Function.Injective periodOneSynthesis := by
  intro a b h
  ext n
  simpa only [periodOneCoefficient_synthesis] using congrArg (fun f => periodOneCoefficient f n) h

end NLS.Fourier
