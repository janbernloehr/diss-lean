import NLS.ZakharovShabat.Potential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The one-derivative domain

We use scalar Fourier modes `exp (i π n x)` on a circle of period two.
Thus differentiation has symbol `i π n`. See the dissertation, Chapter 1,
§2 (the scalar and signed-pair Fourier conventions) and §3, p. 23 (the domain).
The exact graph of the genuine distributional derivative is identified with
these coefficient-space maps in `NLS.Fourier.DistributionDerivative`.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def domainSymbol (m : ℤ → ℂ) (C : ℝ)
    (hm : ∀ n, ‖m n‖ ≤ C * Weight.sobolev 1 n)
    (f : ScalarDomain p) : Coeff p :=
  ⟨fun n => m n * f.val n, by
    apply ((lp.memℓp (WeightedCoeff.weightEquiv _ p f)).norm.const_mul C).mono
    intro n
    simp only [norm_mul, WeightedCoeff.weightEquiv_apply, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ((Weight.sobolev 1).positive n)]
    nlinarith [mul_le_mul_of_nonneg_right (hm n) (norm_nonneg (f.val n))]⟩

private theorem norm_domainSymbol_le (m : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ n, ‖m n‖ ≤ C * Weight.sobolev 1 n) (f : ScalarDomain p) :
    ‖domainSymbol m C hm f‖ ≤ C * ‖f‖ := by
  have h : ‖domainSymbol m C hm f‖ ≤
      ‖(C : ℂ) • WeightedCoeff.weightEquiv _ p f‖ := by
    apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out))
    intro n
    change ‖m n * f.val n‖ ≤ ‖(C : ℂ) * ((Weight.sobolev 1 n : ℂ) * f.val n)‖
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC,
      abs_of_pos ((Weight.sobolev 1).positive n)]
    nlinarith [mul_le_mul_of_nonneg_right (hm n) (norm_nonneg (f.val n))]
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC,
    ← WeightedCoeff.norm_eq] using h

private def domainSymbolCLM (m : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ n, ‖m n‖ ≤ C * Weight.sobolev 1 n) : ScalarDomain p →L[ℂ] Coeff p :=
  LinearMap.mkContinuous
    { toFun := domainSymbol m C hm
      map_add' := by intros; ext n; exact mul_add _ _ _
      map_smul' := by intros; ext n; exact mul_left_comm _ _ _ }
    C (norm_domainSymbol_le m C hC hm)

/-- The inclusion keeps the raw coefficients unchanged. -/
def scalarInclusion : ScalarDomain p →L[ℂ] Coeff p :=
  domainSymbolCLM (fun _ => 1) 1 zero_le_one (by
    intro n
    simp only [norm_one, one_mul, Weight.sobolev_apply, Real.rpow_one]
    exact le_add_of_nonneg_right (abs_nonneg _))

@[simp] theorem scalarInclusion_apply (f : ScalarDomain p) (n : ℤ) :
    scalarInclusion f n = f.val n := one_mul _

theorem norm_scalarInclusion_le (f : ScalarDomain p) : ‖scalarInclusion f‖ ≤ ‖f‖ := by
  change ‖domainSymbol (fun _ => 1) 1 (by intro n; simp) f‖ ≤ ‖f‖
  simpa only [one_mul] using norm_domainSymbol_le (p := p) _ 1 zero_le_one
    (by intro n; simp [Weight.sobolev_apply]) f

theorem scalarInclusion_injective : Function.Injective (scalarInclusion (p := p)) := by
  intro f g h
  apply Subtype.ext
  funext n
  simpa using congrArg (fun a : Coeff p => a n) h

private theorem derivative_symbol_bound (n : ℤ) :
    ‖Complex.I * (Real.pi : ℂ) * n‖ ≤ Real.pi * Weight.sobolev 1 n := by
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, one_mul, Complex.norm_intCast,
    Weight.sobolev_apply, Real.rpow_one]
  simpa only [Real.norm_eq_abs, Int.norm_cast_real] using
    (mul_le_mul_of_nonneg_left (show |(n : ℝ)| ≤ 1 + |(n : ℝ)| by linarith)
      Real.pi_pos.le)

/-- Differentiation for period-two scalar Fourier coefficients. -/
def derivative : ScalarDomain p →L[ℂ] Coeff p :=
  domainSymbolCLM (fun n => Complex.I * (Real.pi : ℂ) * n) Real.pi Real.pi_pos.le
    derivative_symbol_bound

@[simp] theorem derivative_apply (f : ScalarDomain p) (n : ℤ) :
    derivative f n = Complex.I * (Real.pi : ℂ) * n * f.val n := rfl

theorem norm_derivative_le (f : ScalarDomain p) : ‖derivative f‖ ≤ Real.pi * ‖f‖ :=
  norm_domainSymbol_le _ _ Real.pi_pos.le derivative_symbol_bound f

/-- A scalar Fourier mode in the one-derivative domain. -/
def scalarMode (k : ℤ) (c : ℂ) : ScalarDomain p :=
  (WeightedCoeff.weightEquiv _ p).symm
    (lp.single p k ((Weight.sobolev 1 k : ℂ) * c))

omit [Fact (1 ≤ p)] in
@[simp] theorem scalarMode_apply (k : ℤ) (c : ℂ) (n : ℤ) :
    (scalarMode (p := p) k c).val n = if n = k then c else 0 := by
  change (lp.single p k ((Weight.sobolev 1 k : ℂ) * c) : Coeff p) n /
    (Weight.sobolev 1 n : ℂ) = _
  by_cases h : n = k
  · subst n
    simp only [lp.single_apply, Pi.single_apply]
    exact mul_div_cancel_left₀ c ((Weight.sobolev 1).complex_ne_zero k)
  · simp [lp.single_apply, h]

@[simp] theorem scalarInclusion_scalarMode (k : ℤ) (c : ℂ) :
    scalarInclusion (scalarMode (p := p) k c) = lp.single p k c := by
  ext n
  simp [lp.single_apply, Pi.single_apply, eq_comm]

/-- The domain inclusion has dense range for every finite Banach exponent. -/
theorem scalarInclusion_denseRange (hp : p ≠ ⊤) :
    DenseRange (scalarInclusion (p := p)) := by
  intro a
  apply mem_closure_of_tendsto (Coeff.tendsto_truncate hp a)
  apply Filter.Eventually.of_forall
  intro s
  refine ⟨∑ n ∈ s, scalarMode n (a n), ?_⟩
  simp only [map_sum, scalarInclusion_scalarMode, Coeff.truncate]

omit [Fact (1 ≤ p)] in
/-- Control of raw and differentiated coefficients implies one-derivative weighted regularity. -/
theorem memlp_sobolev_weight_of_derivative {a : ℤ → ℂ} (ha : Memℓp a p)
    (hd : Memℓp (fun n : ℤ => Complex.I * (Real.pi : ℂ) * n * a n) p) :
    Memℓp (fun n : ℤ => (Weight.sobolev 1 n : ℂ) * a n) p := by
  apply (ha.norm.add (hd.norm.const_mul Real.pi⁻¹)).mono
  intro n
  have hw : ‖(Weight.sobolev 1 n : ℂ) * a n‖ = (1 + |(n : ℝ)|) * ‖a n‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Weight.sobolev_apply, Real.rpow_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + |(n : ℝ)|)]
  have hdv : ‖Complex.I * (Real.pi : ℂ) * n * a n‖ = Real.pi * |(n : ℝ)| * ‖a n‖ := by
    simp [Complex.norm_intCast, Real.norm_eq_abs, Real.pi_pos.le]
  change ‖(Weight.sobolev 1 n : ℂ) * a n‖ ≤
    ‖a n‖ + Real.pi⁻¹ * ‖Complex.I * (Real.pi : ℂ) * n * a n‖
  rw [hw, hdv]
  field_simp
  exact le_rfl

end NLS.ZakharovShabat
