import NLS.ZakharovShabat.SobolevRiccatiWeakHierarchy

/-! # Actual period-one tempered distributions for weak Riccati densities

Even insertion converts the original unit-period coefficients to the
period-two distribution library. At H⁻¹ this insertion is contractive.
-/
noncomputable section
open NLS.Fourier
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.ZakharovShabat

private def evenSequence (a : ℤ → ℂ) (n : ℤ) : ℂ := if n % 2 = 0 then a (n/2) else 0

private theorem evenSequence_even (a : ℤ → ℂ) (n : ℤ) : evenSequence a (2*n) = a n := by
  simp [evenSequence]

private theorem evenSequence_odd (a : ℤ → ℂ) (n : ℤ) : evenSequence a (2*n+1) = 0 := by
  simp [evenSequence]

private theorem weighted_even_bound (a : WeakRiccatiSpace) (n : ℤ) :
    ‖(Weight.sobolev (-1) n : ℂ)*evenSequence a.val n‖ ≤
      ‖Coeff.periodDouble (WeightedCoeff.weightEquiv (Weight.sobolev (-1)) 2 a) n‖ := by
  by_cases hn : n%2 = 0
  · have he : n = 2*(n/2) := by omega
    rw [he,evenSequence_even,Coeff.periodDouble_even,WeightedCoeff.weightEquiv_apply]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev (-1)).positive _)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
    simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg ((n/2 : ℤ) : ℝ)]
  · have he : n = 2*(n/2)+1 := by omega
    rw [he,evenSequence_odd,Coeff.periodDouble_odd,mul_zero]

/-- The same H⁻¹ coefficients, inserted at even physical frequencies. -/
def weakRiccatiPeriodDouble (a : WeakRiccatiSpace) : WeakRiccatiSpace :=
  ⟨evenSequence a.val,(lp.memℓp (Coeff.periodDouble
    (WeightedCoeff.weightEquiv (Weight.sobolev (-1)) 2 a))).mono' (weighted_even_bound a)⟩

@[simp] theorem weakRiccatiPeriodDouble_even (a : WeakRiccatiSpace) (n : ℤ) :
    (weakRiccatiPeriodDouble a).val (2*n) = a.val n := evenSequence_even _ _

@[simp] theorem weakRiccatiPeriodDouble_odd (a : WeakRiccatiSpace) (n : ℤ) :
    (weakRiccatiPeriodDouble a).val (2*n+1) = 0 := evenSequence_odd _ _

theorem norm_weakRiccatiPeriodDouble_le (a : WeakRiccatiSpace) : ‖weakRiccatiPeriodDouble a‖ ≤ ‖a‖ := by
  have h : ‖WeightedCoeff.weightEquiv (Weight.sobolev (-1)) 2 (weakRiccatiPeriodDouble a)‖ ≤
      ‖Coeff.periodDouble (WeightedCoeff.weightEquiv (Weight.sobolev (-1)) 2 a)‖ :=
    lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (weighted_even_bound a)
  rw [WeightedCoeff.norm_eq,WeightedCoeff.norm_eq]
  simpa only [Coeff.norm_periodDouble] using h

/-- Even insertion is bounded and complex linear in the weak norm. -/
def weakRiccatiPeriodDoubleCLM : WeakRiccatiSpace →L[ℂ] WeakRiccatiSpace :=
  LinearMap.mkContinuous
    { toFun := weakRiccatiPeriodDouble
      map_add' := by
        intro a b
        apply Subtype.ext
        funext n
        change evenSequence (a+b).val n = evenSequence a.val n+evenSequence b.val n
        by_cases hn : n%2 = 0 <;> simp [evenSequence,hn]
      map_smul' := by
        intro c a
        apply Subtype.ext
        funext n
        change evenSequence (c • a).val n = c*evenSequence a.val n
        by_cases hn : n%2 = 0 <;> simp [evenSequence,hn] }
    1 (fun a => by
      change ‖weakRiccatiPeriodDouble a‖ ≤ 1*‖a‖
      simpa only [one_mul] using norm_weakRiccatiPeriodDouble_le a)

/-- Actual tempered-distribution synthesis in the original period-one convention. -/
def weakRiccatiDistribution : WeakRiccatiSpace →L[ℂ] 𝓢'(ℝ, ℂ) :=
  (sobolevDistributionSynthesisCLM (-1)).comp weakRiccatiPeriodDoubleCLM

@[simp] theorem weakRiccatiDistribution_even (a : WeakRiccatiSpace) (n : ℤ) :
    weakRiccatiDistribution a (coefficientTest (2*n)) = a.val n := by
  change sobolevDistributionSynthesisCLM (-1) (weakRiccatiPeriodDouble a) (coefficientTest (2*n)) = _
  rw [sobolevDistributionSynthesisCLM_coefficientTest,weakRiccatiPeriodDouble_even]

@[simp] theorem weakRiccatiDistribution_odd (a : WeakRiccatiSpace) (n : ℤ) :
    weakRiccatiDistribution a (coefficientTest (2*n+1)) = 0 := by
  change sobolevDistributionSynthesisCLM (-1) (weakRiccatiPeriodDouble a) (coefficientTest (2*n+1)) = _
  rw [sobolevDistributionSynthesisCLM_coefficientTest,weakRiccatiPeriodDouble_odd]

/-- Raw weak coefficients faithfully determine the represented distribution. -/
theorem weakRiccatiDistribution_injective : Function.Injective weakRiccatiDistribution := by
  intro a b h
  apply Subtype.ext
  funext n
  simpa only [weakRiccatiDistribution_even] using congrArg (fun T : 𝓢'(ℝ, ℂ) => T (coefficientTest (2*n))) h

/-- The new coefficient derivative is Mathlib's actual tempered-distribution derivative. -/
theorem weakRiccatiDistribution_derivative (a : ScalarSobolev 0) :
    weakRiccatiDistribution (weakRiccatiDerivative a) =
      TemperedDistribution.derivCLM ℂ (distributionSynthesis
        (Coeff.periodDouble (WeightedCoeff.weightEquiv (Weight.sobolev (0 : ℕ)) 2 a))) := by
  ext g
  change sobolevDistributionSynthesisCLM (-1) (weakRiccatiPeriodDouble (weakRiccatiDerivative a)) g = _
  rw [sobolevDistributionSynthesisCLM_apply,distributionDerivative_apply]
  apply tsum_congr
  intro n
  by_cases hn : n%2 = 0
  · have he : n = 2*(n/2) := by omega
    rw [he,weakRiccatiPeriodDouble_even,weakRiccatiDerivative_apply,Coeff.periodDouble_even,
      WeightedCoeff.weightEquiv_apply]
    simp only [Nat.cast_zero,Weight.sobolev_zero_apply,Complex.ofReal_one,one_mul,Int.cast_mul,Int.cast_ofNat]
    ring
  · have he : n = 2*(n/2)+1 := by omega
    rw [he,weakRiccatiPeriodDouble_odd,Coeff.periodDouble_odd]
    simp

end NLS.ZakharovShabat
