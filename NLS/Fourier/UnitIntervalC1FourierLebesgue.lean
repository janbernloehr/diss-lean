import NLS.Fourier.UnitIntervalCoefficientDecay
import NLS.SequenceSpaces.SobolevEmbedding

/-! # Uniform Fourier–Lebesgue bounds for C¹ unit-interval functions

The inverse bracket belongs to every ℓq with q > 1. Its norm provides
one explicit constant, independent of the function and without requiring
matching endpoints. The coefficients are the original Fourier integrals.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Fourier

private theorem coefficient_majorant (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ A)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv f t‖ ≤ D) (n : ℤ) :
    ‖intervalFourierCoefficient 1 f n‖ ≤ ‖((2*A+D : ℝ) : ℂ)*(Weight.sobolev 1 n : ℂ)⁻¹‖ := by
  simpa only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 2*A+D),Weight.sobolev_apply,Real.rpow_one,
    abs_of_pos (by positivity : 0 < 1+|(n : ℝ)|),div_eq_mul_inv] using
    norm_unitIntervalFourierCoefficient_le_bracket f hf A D hA hD hb hd n

/-- Quantitative C¹ bounds give membership at every Fourier–Lebesgue exponent above one. -/
theorem memlp_unitIntervalFourierCoefficient_of_bounds {q : ℝ≥0∞} (hq : 1 < q)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ A)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv f t‖ ≤ D) :
    Memℓp (intervalFourierCoefficient 1 f) q :=
  ((Weight.inverse_sobolev_one_memlp hq).const_mul ((2*A+D : ℝ) : ℂ)).mono'
    (coefficient_majorant f hf A D hA hD hb hd)

/-- Every C¹ function has actual unit-interval Fourier coefficients in ℓq for every q > 1. -/
theorem memlp_unitIntervalFourierCoefficient_of_contDiff {q : ℝ≥0∞} (hq : 1 < q)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) : Memℓp (intervalFourierCoefficient 1 f) q := by
  obtain ⟨A,hA⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨D,hD⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (contDiff_one_iff_deriv.mp hf).2.continuousOn
  exact memlp_unitIntervalFourierCoefficient_of_bounds hq f hf A D
    ((norm_nonneg (f 0)).trans (hA 0 (by simp)))
    ((norm_nonneg (deriv f 0)).trans (hD 0 (by simp))) hA hD

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- A constant depending only on the target exponent. -/
def unitIntervalC1FourierConstant (hq : 1 < q) : ℝ :=
  ‖WeightedCoeff.inverseWeight (Weight.sobolev 1) (Weight.inverse_sobolev_one_memlp hq)‖

theorem unitIntervalC1FourierConstant_nonneg (hq : 1 < q) : 0 ≤ unitIntervalC1FourierConstant hq :=
  norm_nonneg _

/-- The original Fourier integrals, bundled as a Fourier–Lebesgue sequence. -/
def unitIntervalC1Coefficients (hq : 1 < q) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) : Coeff q :=
  ⟨intervalFourierCoefficient 1 f,memlp_unitIntervalFourierCoefficient_of_contDiff hq f hf⟩

omit [Fact (1 ≤ q)] in
@[simp] theorem unitIntervalC1Coefficients_apply (hq : 1 < q) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (n : ℤ) :
    unitIntervalC1Coefficients hq f hf n = intervalFourierCoefficient 1 f n := rfl

/-- The quantitative Fourier–Lebesgue bound, valid also for the infinity exponent. -/
theorem norm_unitIntervalC1Coefficients_le (hq : 1 < q)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ A)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv f t‖ ≤ D) :
    ‖unitIntervalC1Coefficients hq f hf‖ ≤ (2*A+D)*unitIntervalC1FourierConstant hq := by
  have h := lp.norm_mono (zero_lt_one.trans hq).ne'
    (x := unitIntervalC1Coefficients hq f hf)
    (y := ((2*A+D : ℝ) : ℂ) • WeightedCoeff.inverseWeight (Weight.sobolev 1)
      (Weight.inverse_sobolev_one_memlp hq)) (coefficient_majorant f hf A D hA hD hb hd)
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 2*A+D),unitIntervalC1FourierConstant] using h

/-- The Fourier–Lebesgue construction agrees with the existing Parseval construction at q = 2. -/
theorem unitIntervalC1Coefficients_two (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    unitIntervalC1Coefficients (q := 2) (by norm_num) f hf =
      unitIntervalL2Coefficients f hf.continuous := by ext n; rfl

end NLS.Fourier
