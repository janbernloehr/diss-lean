import NLS.Fourier.PhysicalMidpointHilbertRows
import NLS.Fourier.AbsoluteSampledRows
import NLS.ComplexAnalysis.ProductErrorLp

/-!
# Quadratic remainder of a physical midpoint product

Linear separation bounds the absolute first-order row by a positive
reciprocal-kernel convolution in the doubled exponent.  The general
quadratic product estimate then places the nonlinear remainder back in
the original coefficient exponent.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ 2*p) := ⟨NLS.one_le_double_exponent Fact.out⟩
local instance : (2*p).HolderTriple (2*p) p := NLS.holderTriple_double p

/-- The off-diagonal physical midpoint factor on selected rows. -/
def physicalMidpointTerm (S : Set ℤ) (τ z : ℤ → ℂ)
    (a : Coeff p) (n m : ℤ) : ℂ := by
  classical
  exact if n ∈ S then (if m = n then 0 else a m/(τ m-z n)) else 0

omit [Fact (1 ≤ p)] in
/-- Separation bounds each absolute physical factor by the reciprocal
kernel with the same index difference. -/
theorem norm_physicalMidpointTerm_le
    {S : Set ℤ} {C R : ℝ} {τ z : ℤ → ℂ}
    (h : SeparatedReciprocalRows S C R τ z)
    (a : Coeff p) {n : ℤ} (hn : n ∈ S) (m : ℤ) :
    ‖physicalMidpointTerm S τ z a n m‖ ≤
      C*(‖a m‖*‖hilbertKernel (n-m)‖) := by
  classical
  by_cases hmn : m = n
  · subst m
    simp [physicalMidpointTerm, hn, hilbertKernel]
  have hd : 0 < |((n-m : ℤ) : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast sub_ne_zero.mpr (Ne.symm hmn)
  have hCpos : 0 < C := h.2.1
  have hden : 0 < ‖τ m-z n‖ := by
    have hs := h.2.2.2.1 n hn m hmn
    nlinarith
  have hinv : ‖τ m-z n‖⁻¹ ≤ C*|((n-m : ℤ) : ℝ)|⁻¹ := by
    calc
      ‖τ m-z n‖⁻¹ = 1/‖τ m-z n‖ := by ring
      _ ≤ C/|((n-m : ℤ) : ℝ)| :=
        (div_le_div_iff₀ hden hd).mpr (by simpa using h.2.2.2.1 n hn m hmn)
      _ = C*|((n-m : ℤ) : ℝ)|⁻¹ := by ring
  have hk : ‖hilbertKernel (n-m)‖ = |((n-m : ℤ) : ℝ)|⁻¹ := by
    simp only [hilbertKernel, norm_neg, norm_inv, Complex.norm_intCast]
  simp only [physicalMidpointTerm, if_pos hn, if_neg hmn, norm_div, hk]
  calc
    ‖a m‖/‖τ m-z n‖ = ‖a m‖*‖τ m-z n‖⁻¹ := by ring
    _ ≤ ‖a m‖*(C*|((n-m : ℤ) : ℝ)|⁻¹) :=
      mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
    _ = C*(‖a m‖*|((n-m : ℤ) : ℝ)|⁻¹) := by ring

/-- Every selected absolute row is summable at all finite Banach
exponents, including `p=1`. -/
theorem summable_norm_physicalMidpointTerm
    (hp : p ≠ ⊤)
    {S : Set ℤ} {C R : ℝ} {τ z : ℤ → ℂ}
    (h : SeparatedReciprocalRows S C R τ z)
    (a : Coeff p) (n : ℤ) :
    Summable (fun m : ℤ => ‖physicalMidpointTerm S τ z a n m‖) := by
  classical
  by_cases hn : n ∈ S
  · have hbase := summable_absoluteSampledRow hp a n
    apply (hbase.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _)
    exact norm_physicalMidpointTerm_le h a hn
  · simpa only [physicalMidpointTerm, if_neg hn, norm_zero] using
      (summable_zero : Summable (fun _ : ℤ => (0 : ℝ)))

/-- A doubled-exponent majorant for every absolute physical row. -/
def physicalMidpointAbsoluteMajorant (hp : p ≠ ⊤)
    (C : ℝ) (a : Coeff p) : Coeff (2*p) :=
  ((C/2 : ℝ) : ℂ) • absoluteSampledRowMajorant hp a

/-- The majorant coefficient is exactly the scaled absolute reciprocal
kernel row. -/
theorem norm_physicalMidpointAbsoluteMajorant_apply
    (hp : p ≠ ⊤) (C : ℝ) (hC : 0 ≤ C)
    (a : Coeff p) (n : ℤ) :
    ‖physicalMidpointAbsoluteMajorant hp C a n‖ =
      C*∑' m : ℤ, ‖a m‖*‖hilbertKernel (n-m)‖ := by
  rw [physicalMidpointAbsoluteMajorant, lp.coeFn_smul, Pi.smul_apply,
    norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hC (by norm_num)),
    norm_absoluteSampledRowMajorant_apply]
  ring

/-- The absolute physical row is pointwise bounded by its
doubled-exponent majorant. -/
theorem tsum_norm_physicalMidpointTerm_le_majorant
    (hp : p ≠ ⊤)
    {S : Set ℤ} {C R : ℝ} {τ z : ℤ → ℂ}
    (h : SeparatedReciprocalRows S C R τ z)
    (a : Coeff p) (n : ℤ) :
    (∑' m : ℤ, ‖physicalMidpointTerm S τ z a n m‖) ≤
      ‖physicalMidpointAbsoluteMajorant hp C a n‖ := by
  classical
  by_cases hn : n ∈ S
  · rw [norm_physicalMidpointAbsoluteMajorant_apply hp C h.2.1.le]
    have hu := summable_norm_physicalMidpointTerm hp h a n
    have hb := (summable_absoluteSampledRow hp a n).mul_left C
    rw [← tsum_mul_left]
    exact hu.tsum_le_tsum (norm_physicalMidpointTerm_le h a hn) hb
  · simp only [physicalMidpointTerm, if_neg hn, norm_zero, tsum_zero]
    exact norm_nonneg _

/-- The quadratic error of the physical midpoint product as an `ℓp`
sequence, with the signed first-order sum removed. -/
def physicalMidpointProductRemainder
    (hp : p ≠ ⊤)
    {S : Set ℤ} {C R : ℝ} {τ z : ℤ → ℂ}
    (h : SeparatedReciprocalRows S C R τ z)
    (a : Coeff p) : Coeff p :=
  NLS.ComplexAnalysis.productRemainderCoeff (p := p)
    (physicalMidpointTerm S τ z a)
    (summable_norm_physicalMidpointTerm hp h a)
    (physicalMidpointAbsoluteMajorant hp C a)
    (tsum_norm_physicalMidpointTerm_le_majorant hp h a)

/-- The nonlinear error is quadratic in the input norm, uniformly over
all selected sampling points. -/
theorem norm_physicalMidpointProductRemainder_le
    (hp : p ≠ ⊤)
    {S : Set ℤ} {C R : ℝ} {τ z : ℤ → ℂ}
    (h : SeparatedReciprocalRows S C R τ z)
    (a : Coeff p) :
    ‖physicalMidpointProductRemainder hp h a‖ ≤
      Real.exp ((C/2)*absoluteSampledRowConstant hp*‖a‖)*
        ((C/2)*absoluteSampledRowConstant hp*‖a‖)^2 := by
  have hC : 0 ≤ C/2 := div_nonneg h.2.1.le (by norm_num)
  have hA : ‖physicalMidpointAbsoluteMajorant hp C a‖ ≤
      (C/2)*absoluteSampledRowConstant hp*‖a‖ := by
    rw [physicalMidpointAbsoluteMajorant, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hC]
    exact (mul_le_mul_of_nonneg_left (norm_absoluteSampledRowMajorant_le hp a) hC).trans_eq
      (by ring)
  have hr := NLS.ComplexAnalysis.norm_productRemainderCoeff_le (p := p)
    (physicalMidpointTerm S τ z a)
    (summable_norm_physicalMidpointTerm hp h a)
    (physicalMidpointAbsoluteMajorant hp C a)
    (tsum_norm_physicalMidpointTerm_le_majorant hp h a)
  exact hr.trans (mul_le_mul (Real.exp_le_exp.mpr hA)
    (pow_le_pow_left₀ (norm_nonneg _) hA 2)
      (sq_nonneg _) (Real.exp_nonneg _))

end NLS.Fourier
