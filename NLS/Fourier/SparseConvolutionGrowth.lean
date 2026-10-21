import NLS.Fourier.PeriodicDistributionFourierGrowth
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Polynomial inputs with finite but superpolynomial Fourier convolutions

The left sequence is k on k=4^j and zero elsewhere. The right sequence
is one on k=j-4^j and zero elsewhere. Each individual convolution has
finite support, but its value at n>=0 is at least 4^n.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.Fourier

def sparseConvolutionLeft (k : ℤ) : ℂ := by
  classical
  exact if ∃ j : ℕ, k = (4:ℤ)^j then (k:ℂ) else 0

def sparseConvolutionRight (k : ℤ) : ℂ := by
  classical
  exact if ∃ j : ℕ, k = (j:ℤ)-(4:ℤ)^j then 1 else 0

theorem two_mul_add_one_le_four_pow (j : ℕ) : 2*(j:ℤ)+1 ≤ (4:ℤ)^j := by
  induction j with
  | zero => norm_num
  | succ j hj =>
    rw [pow_succ]
    push_cast
    nlinarith [show (0:ℤ) ≤ j by positivity]

theorem four_pow_gap (i j : ℕ) (hij : i < j) : (4:ℤ)^i+2*(j:ℤ) ≤ (4:ℤ)^j := by
  cases j with
  | zero => omega
  | succ j =>
    have hp : (4:ℤ)^i ≤ (4:ℤ)^j := pow_le_pow_right₀ (by norm_num) (by omega)
    have hj := two_mul_add_one_le_four_pow j
    rw [pow_succ]
    push_cast
    nlinarith [show (0:ℤ) ≤ j by positivity]

/-- A nonzero convolution term has both sparse labels bounded by the output frequency. -/
theorem sparseConvolution_indices_le (m : ℤ) (i j : ℕ)
    (hm : m = (4:ℤ)^i+(j:ℤ)-(4:ℤ)^j) : i ≤ m.natAbs ∧ j ≤ m.natAbs := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have hg := four_pow_gap i j hij
    have hmj : m ≤ -(j:ℤ) := by omega
    have habs : -(m.natAbs:ℤ) ≤ m := by
      simpa only [Int.natCast_natAbs] using neg_abs_le m
    constructor <;> omega
  · subst j
    simp only [add_sub_cancel_left] at hm
    subst m
    simp
  · have hg := four_pow_gap j i hij
    have hmi : (i:ℤ) ≤ m := by omega
    have habs : m ≤ (m.natAbs:ℤ) := Int.le_natAbs
    constructor <;> omega

theorem sparseConvolutionLeft_norm_le (k : ℤ) : ‖sparseConvolutionLeft k‖ ≤ |(k:ℝ)| := by
  unfold sparseConvolutionLeft
  split_ifs <;> simp

theorem sparseConvolutionRight_norm_le (k : ℤ) : ‖sparseConvolutionRight k‖ ≤ 1 := by
  unfold sparseConvolutionRight
  split_ifs <;> norm_num

/-- Both input sequences have the polynomial bounds required for actual distributions. -/
theorem sparseConvolution_inputs_polynomial :
    Asymptotics.IsBigO cofinite sparseConvolutionLeft (fun k : ℤ => |(k:ℝ)|^1) ∧
    Asymptotics.IsBigO cofinite sparseConvolutionRight (fun k : ℤ => |(k:ℝ)|^0) := by
  constructor
  · apply polynomial_isBigO_of_bracket_bound _ 1 1 (by norm_num)
    intro k
    simpa only [one_mul,pow_one] using (sparseConvolutionLeft_norm_le k).trans (by linarith)
  · apply polynomial_isBigO_of_bracket_bound _ 0 1 (by norm_num)
    intro k
    simpa only [pow_zero,mul_one] using sparseConvolutionRight_norm_le k

/-- Every individual coefficient sum has finite support. -/
theorem finite_support_sparseConvolution (m : ℤ) :
    (Function.support (fun k : ℤ => sparseConvolutionLeft (m-k)*sparseConvolutionRight k)).Finite := by
  classical
  apply (Finset.finite_toSet ((Finset.range (m.natAbs+1)).image (fun j : ℕ => (j:ℤ)-(4:ℤ)^j))).subset
  intro k hk
  change sparseConvolutionLeft (m-k)*sparseConvolutionRight k ≠ 0 at hk
  have hl : ∃ i : ℕ, m-k = (4:ℤ)^i := by
    by_contra h
    simp [sparseConvolutionLeft,h] at hk
  have hr : ∃ j : ℕ, k = (j:ℤ)-(4:ℤ)^j := by
    by_contra h
    simp [sparseConvolutionRight,h] at hk
  obtain ⟨i,hi⟩ := hl
  obtain ⟨j,hj⟩ := hr
  have hb := (sparseConvolution_indices_le m i j (by omega)).2
  exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by omega),hj.symm⟩

theorem summable_sparseConvolution (m : ℤ) :
    Summable (fun k : ℤ => sparseConvolutionLeft (m-k)*sparseConvolutionRight k) :=
  summable_of_hasFiniteSupport (finite_support_sparseConvolution m)

def sparseConvolutionValue (m : ℤ) : ℂ :=
  ∑' k : ℤ, sparseConvolutionLeft (m-k)*sparseConvolutionRight k

theorem sparseConvolutionLeft_re_nonneg (k : ℤ) : 0 ≤ (sparseConvolutionLeft k).re := by
  unfold sparseConvolutionLeft
  split_ifs with h
  · obtain ⟨j,rfl⟩ := h
    simp only [Complex.intCast_re]
    positivity
  · norm_num

theorem sparseConvolution_term_re_nonneg (m k : ℤ) :
    0 ≤ (sparseConvolutionLeft (m-k)*sparseConvolutionRight k).re := by
  unfold sparseConvolutionRight
  split_ifs
  · simpa only [mul_one] using sparseConvolutionLeft_re_nonneg (m-k)
  · simp

/-- A single diagonal contribution already forces exponential output growth. -/
theorem four_pow_le_sparseConvolution (m : ℕ) : (4:ℝ)^m ≤ (sparseConvolutionValue m).re := by
  have hs := Complex.reCLM.summable (summable_sparseConvolution (m:ℤ))
  have h := hs.le_tsum ((m:ℤ)-(4:ℤ)^m) (fun k _ => sparseConvolution_term_re_nonneg (m:ℤ) k)
  have he : (sparseConvolutionLeft ((m:ℤ)-((m:ℤ)-(4:ℤ)^m))*
      sparseConvolutionRight ((m:ℤ)-(4:ℤ)^m)).re = (4:ℝ)^m := by
    rw [sub_sub_cancel,sparseConvolutionLeft,if_pos ⟨m,rfl⟩,
      sparseConvolutionRight,if_pos ⟨m,rfl⟩,mul_one]
    norm_cast
  change (sparseConvolutionLeft ((m:ℤ)-((m:ℤ)-(4:ℤ)^m))*
    sparseConvolutionRight ((m:ℤ)-(4:ℤ)^m)).re ≤
      ∑' k : ℤ, (sparseConvolutionLeft ((m:ℤ)-k)*sparseConvolutionRight k).re at h
  rw [he] at h
  simpa only [sparseConvolutionValue,Complex.re_tsum (summable_sparseConvolution (m:ℤ))] using h

/-- Convergence of every coefficient does not make its output polynomially bounded. -/
theorem not_polynomial_sparseConvolution (N : ℕ) :
    ¬ Asymptotics.IsBigO cofinite sparseConvolutionValue (fun m : ℤ => |(m:ℝ)|^N) := by
  intro hN
  obtain ⟨C,hC,hb⟩ := hN.exists_pos
  have he := (tendsto_natCast_atTop_atTop (R := ℤ)).eventually (atTop_le_cofinite hb.bound)
  have hbound : ∀ᶠ m : ℕ in atTop, ‖sparseConvolutionValue m‖ ≤ C*(m:ℝ)^N := by
    filter_upwards [he] with m hm
    simpa only [Int.cast_natCast,norm_pow,Real.norm_eq_abs,abs_abs,Nat.abs_cast] using hm
  have ht : Tendsto (fun m : ℕ => C*((m:ℝ)^N/(4:ℝ)^m)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt N (by norm_num : (1:ℝ)<4)).const_mul C
  have hone : ∀ᶠ m : ℕ in atTop, 1 ≤ C*((m:ℝ)^N/(4:ℝ)^m) := by
    filter_upwards [hbound] with m hm
    have hle := (four_pow_le_sparseConvolution m).trans ((Complex.re_le_norm _).trans hm)
    rw [← mul_div_assoc]
    exact (le_div_iff₀ (by positivity : (0:ℝ)<4^m)).mpr (by simpa only [one_mul] using hle)
  have hfalse : (1:ℝ) ≤ 0 := ge_of_tendsto ht hone
  norm_num at hfalse

end NLS.Fourier
