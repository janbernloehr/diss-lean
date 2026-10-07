import NLS.SequenceSpaces.PeriodDoubling
import NLS.ZakharovShabat.Domain

/-! # Period doubling in the one-derivative Hilbert norm

A period-one frequency n occupies the even period-two frequency 2n.
The weighted inclusion is bounded by two, and differentiation commutes
with insertion when the period-one derivative carries its factor two.
-/
noncomputable section
open Complex
namespace NLS.Coeff
open ZakharovShabat

private theorem periodDouble_weight_bound (a : ScalarDomain 2) (n : ℤ) :
    ‖(Weight.sobolev 1 n:ℂ) * periodDouble (scalarInclusion a) n‖ ≤
      ‖(2:ℂ) * periodDouble (WeightedCoeff.weightEquiv (Weight.sobolev 1) 2 a) n‖ := by
  by_cases hn : n % 2 = 0
  · have he : n = 2*(n/2) := by omega
    rw [he,periodDouble_even,periodDouble_even]
    simp only [scalarInclusion_apply,WeightedCoeff.weightEquiv_apply,norm_mul,
      Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,Weight.sobolev_apply,Real.rpow_one,
      Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ 2),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + 2*|((n/2:ℤ):ℝ)|),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + |((n/2:ℤ):ℝ)|)]
    nlinarith [norm_nonneg (a.val (n/2))]
  · have he : n = 2*(n/2)+1 := by omega
    rw [he,periodDouble_odd,periodDouble_odd,mul_zero,mul_zero]

/-- The same original source coefficients, inserted at the even frequencies. -/
def periodDoubleSobolev (a : ScalarDomain 2) : ScalarDomain 2 :=
by
  refine ⟨fun n => periodDouble (scalarInclusion a) n,?_⟩
  have hm : Memℓp (fun n : ℤ => (2:ℂ) * periodDouble (WeightedCoeff.weightEquiv (Weight.sobolev 1) 2 a) n) 2 :=
    (lp.memℓp (periodDouble (WeightedCoeff.weightEquiv (Weight.sobolev 1) 2 a))).const_mul (2:ℂ)
  exact hm.mono' (periodDouble_weight_bound a)


@[simp] theorem periodDoubleSobolev_apply (a : ScalarDomain 2) (n : ℤ) :
    (periodDoubleSobolev a).val n = periodDouble (scalarInclusion a) n := rfl

/-- Changing the period costs at most a factor two in the one-derivative norm. -/
theorem norm_periodDoubleSobolev_le (a : ScalarDomain 2) : ‖periodDoubleSobolev a‖ ≤ 2*‖a‖ := by
  have h : ‖WeightedCoeff.weightEquiv (Weight.sobolev 1) 2 (periodDoubleSobolev a)‖ ≤
      ‖(2:ℂ) • periodDouble (WeightedCoeff.weightEquiv (Weight.sobolev 1) 2 a)‖ :=
    lp.norm_mono (by norm_num) (periodDouble_weight_bound a)
  simpa only [norm_smul,Complex.norm_ofNat,norm_periodDouble,← WeightedCoeff.norm_eq] using h

/-- Period doubling as a bounded linear map on the Sobolev domain. -/
def periodDoubleSobolevCLM : ScalarDomain 2 →L[ℂ] ScalarDomain 2 :=
  LinearMap.mkContinuous {
    toFun := periodDoubleSobolev
    map_add' := by
      intro a b
      apply Subtype.ext
      funext n
      change periodDouble (scalarInclusion (a + b)) n =
        periodDouble (scalarInclusion a) n + periodDouble (scalarInclusion b) n
      simp only [map_add, lp.coeFn_add, Pi.add_apply]
    map_smul' := by
      intro c a
      apply Subtype.ext
      funext n
      change periodDouble (scalarInclusion (c • a)) n = c * periodDouble (scalarInclusion a) n
      simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  } 2 norm_periodDoubleSobolev_le

/-- The period-two derivative of the doubled function has the original
period-one symbol 2πin on the even frequencies. -/
theorem derivative_periodDoubleSobolev (a : ScalarDomain 2) :
    derivative (periodDoubleSobolev a) = periodDouble ((2:ℂ) • derivative a) := by
  ext n
  by_cases hn : n % 2 = 0
  · have he : n = 2*(n/2) := by omega
    rw [he,derivative_apply,periodDoubleSobolev_apply,periodDouble_even,periodDouble_even]
    simp only [scalarInclusion_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,derivative_apply]
    push_cast
    ring
  · have he : n = 2*(n/2)+1 := by omega
    rw [he,derivative_apply,periodDoubleSobolev_apply,periodDouble_odd,periodDouble_odd,mul_zero]

/-- A signed original mode occupies exactly twice its frequency. -/
@[simp] theorem periodDoubleSobolev_scalarMode (n : ℤ) (c : ℂ) :
    periodDoubleSobolev (scalarMode n c) = scalarMode (2*n) c := by
  apply Subtype.ext
  funext k
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he, periodDoubleSobolev_apply, periodDouble_even, scalarInclusion_apply]
    simp only [scalarMode_apply]
    by_cases h : k / 2 = n
    · simp only [h]
    · rw [if_neg h, if_neg (by omega)]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he, periodDoubleSobolev_apply, periodDouble_odd, scalarMode_apply]
    rw [if_neg (by omega)]

end NLS.Coeff
