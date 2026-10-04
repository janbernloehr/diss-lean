import NLS.Fourier.PeriodOneCoefficients
import NLS.Fourier.SchwartzPeriodizationSmooth
import NLS.SequenceSpaces.SobolevDerivative
import NLS.SequenceSpaces.SobolevEmbedding

/-! # Smooth period-one synthesis from all Sobolev weights

Absolute summability of the derivative series justifies differentiation
at every real point. All finite Sobolev weights at any finite Banach
exponent supply these derivative series and hence a smooth periodic function.
-/
noncomputable section
open Complex
open scoped ENNReal ContDiff
namespace NLS.Fourier

/-- Absolutely convergent period-one derivative coefficients give the actual
classical derivative, including at period endpoints. -/
theorem hasDerivAt_periodOneSynthesis_of_coefficients (a b : Coeff 1)
    (h : ∀ n : ℤ, b n = 2*I*(Real.pi : ℂ)*n*a n) (x : ℝ) :
    HasDerivAt (periodOneSynthesis a) (periodOneSynthesis b x) x := by
  have hb := (lp.memℓp b).norm.summable_of_one
  have hd (n : ℤ) (y : ℝ) :
      HasDerivAt (fun t => a n*wave (2*n) t) (b n*wave (2*n) y) y := by
    convert! (hasDerivAt_wave (2*n) y).const_mul (a n) using 1
    rw [h n]
    push_cast
    ring
  have hn (n : ℤ) (y : ℝ) : ‖b n*wave (2*n) y‖ ≤ ‖b n‖ := by
    simp [wave,Complex.norm_exp]
  have ha : Summable (fun n : ℤ => a n*wave (2*n) (0 : ℝ)) := by
    simpa using (lp.memℓp a).summable_of_one
  simpa only [← periodOneSynthesis_eq_tsum] using hasDerivAt_tsum hb hd hn ha x

/-- A full chain of absolutely summable derivative coefficients gives smoothness. -/
theorem contDiff_periodOneSynthesis_of_derivative_chain (a : ℕ → Coeff 1)
    (h : ∀ k : ℕ, ∀ n : ℤ, a (k+1) n = 2*I*(Real.pi : ℂ)*n*a k n) :
    ContDiff ℝ ∞ (periodOneSynthesis (a 0)) := by
  have hd (k : ℕ) : deriv (periodOneSynthesis (a k)) = periodOneSynthesis (a (k+1)) :=
    funext (fun x => (hasDerivAt_periodOneSynthesis_of_coefficients _ _ (h k) x).deriv)
  have hs (m k : ℕ) : ContDiff ℝ m (periodOneSynthesis (a k)) := by
    induction m generalizing k with
    | zero => exact contDiff_zero.mpr (continuous_periodOneSynthesis _)
    | succ m ih =>
      rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
      refine ⟨fun x => (hasDerivAt_periodOneSynthesis_of_coefficients _ _ (h k) x).differentiableAt,?_,?_⟩
      · simp
      · rw [hd k]
        exact ih (k+1)
  exact contDiff_infty.mpr (fun m => hs m 0)

private def derivativeSequence (a : ℤ → ℂ) : ℕ → ℤ → ℂ
  | 0 => a
  | k+1 => fun n => 2*I*(Real.pi : ℂ)*n*derivativeSequence a k n

/-- All Sobolev weights at a finite exponent produce an everywhere smooth
representative of the absolutely convergent period-one Fourier series. -/
theorem contDiff_periodOneSynthesis_of_all_sobolev
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (a : Coeff 1)
    (hall : ∀ s : ℝ, 0 ≤ s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*a n) p) :
    ContDiff ℝ ∞ (periodOneSynthesis a) := by
  have hD (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
      Memℓp (fun n => (Weight.sobolev s n : ℂ)*derivativeSequence a k n) p := by
    induction k generalizing s with
    | zero => exact hall s hs
    | succ k ih =>
      let b : WeightedCoeff (Weight.sobolev (s+1)) p := ⟨_,ih (s+1) (by linarith)⟩
      have hd := (WeightedCoeff.sobolevDerivative s b).property
      change Memℓp (fun n => (Weight.sobolev s n : ℂ)*(I*(Real.pi : ℂ)*n*derivativeSequence a k n)) p at hd
      convert! hd.const_mul (2 : ℂ) using 1
      funext n
      simp only [derivativeSequence]
      ring
  let d : ℕ → Coeff 1 := fun k => WeightedCoeff.sobolevToL1CLM p hp ⟨_,hD k 1 zero_le_one⟩
  have hd (k : ℕ) (n : ℤ) : d k n = derivativeSequence a k n :=
    WeightedCoeff.sobolevToL1CLM_apply p hp _ n
  have hchain (k : ℕ) (n : ℤ) : d (k+1) n = 2*I*(Real.pi : ℂ)*n*d k n := by
    rw [hd,hd]
    rfl
  have hzero : d 0 = a := by
    ext n
    exact hd 0 n
  simpa only [hzero] using contDiff_periodOneSynthesis_of_derivative_chain d hchain

end NLS.Fourier
