import NLS.DifferentialPolynomial.WeightedJetReduction
import NLS.KdV.HillRiccatiRemainder
import NLS.DifferentialPolynomial.BalancedJetProduct

/-! # Source Lemma 7: the exact half kinetic term and one lower-jet scalar polynomial at every order. -/

noncomputable section
open MvPolynomial Complex MeasureTheory NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.KdV

theorem exists_hillRiccatiCubicRemainder_reduction (m : ℕ) (hm : 1 ≤ m) :
    HasWeightedJetReduction hillJetWeight m (2*(m : ℤ)+4) (2*(m : ℤ)-2)
      (hillRiccatiCubicRemainder (2*m+2)) := by
  apply exists_weighted_jet_reduction
  · intro v
    simp only [hillJetWeight, nextJet, Nat.cast_add, Nat.cast_one]
    omega
  · exact hm
  · convert! hillRiccatiCubicRemainder_homogeneous (2*m+2) using 1
  · convert hillRiccatiCubicRemainder_derivativeOrder (2*m+2) using 1
    push_cast
    ring

theorem integral_scalar_jet_product (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) (i j m : ℕ) (hij : i+j = 2*m) :
    (∫ x in (0 : ℝ)..1, iteratedDeriv i q x * iteratedDeriv j q x) =
      (-1 : ℂ)^(i+m) * ∫ x in (0 : ℝ)..1, (iteratedDeriv m q x)^2 := by
  obtain ⟨r, hr⟩ := exists_balanced_jet_product 0 i j
  have he := integral_evaluate_eq_of_total_derivative q q hq hq hp hp _ _ r hr
  simp only [evaluate_mul, evaluate_C, evaluate_X, Pi.mul_apply, Nat.zero_add,
    iteratedDeriv_zero, Bool.false_eq_true, ↓reduceIte,
    intervalIntegral.integral_const_mul, mul_assoc, hij] at he
  have hb := integral_balanced_derivatives q q hq hq hp hp m
  simp only [← pow_two] at hb
  have hpow : (-1 : ℂ)^i * (-1 : ℂ)^i = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((-1 : ℂ)^i * (-1 : ℂ)^i) *
        (∫ x in (0 : ℝ)..1, iteratedDeriv i q x * iteratedDeriv j q x) := by rw [hpow, one_mul]
    _ = (-1 : ℂ)^i * (∫ x in (0 : ℝ)..1, q x * iteratedDeriv (2*m) q x) := by rw [he]; ring
    _ = _ := by rw [hb, ← mul_assoc, ← pow_add]

theorem integral_hillRiccatiQuadratic_recurrence (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) (n : ℕ) :
    (∫ x in (0 : ℝ)..1, evaluate q 0 (hillRiccatiQuadratic (n+2)) x) =
      -∑ ij ∈ Finset.antidiagonal n,
        ∫ x in (0 : ℝ)..1, evaluate q 0 (hillRiccatiLinear ij.1*hillRiccatiLinear ij.2) x := by
  have he : hillRiccatiQuadratic (n+2) =
      -(∑ ij ∈ Finset.antidiagonal n, hillRiccatiLinear ij.1*hillRiccatiLinear ij.2) +
        spatialDerivative (-hillRiccatiQuadratic (n+1)) := by
    rw [hillRiccatiQuadratic_recurrence, map_neg]
    ring
  have hi := integral_evaluate_eq_of_total_derivative q 0 hq contDiff_const hp
    (fun _ => rfl) _ _ _ he
  rw [hi]
  simp only [evaluate_neg, Pi.neg_apply, intervalIntegral.integral_neg]
  congr 1
  have heval : evaluate q 0
      (∑ ij ∈ Finset.antidiagonal n, hillRiccatiLinear ij.1*hillRiccatiLinear ij.2) =
      fun x => ∑ ij ∈ Finset.antidiagonal n,
        evaluate q 0 (hillRiccatiLinear ij.1*hillRiccatiLinear ij.2) x := by
    funext x
    simp [evaluate]
  rw [heval]
  exact intervalIntegral.integral_finsetSum (fun ij _ =>
    (continuous_evaluate q 0 hq contDiff_const _).intervalIntegrable 0 1)

theorem sum_neg_one_even_range (m : ℕ) :
    (∑ i ∈ Finset.range (2*m+1), (-1 : ℂ)^i) = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1)+1 = (2*m+1)+1+1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have hodd : (-1 : ℂ)^(2*m+1) = -1 := by
      rw [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
    have heven : (-1 : ℂ)^(2*m+1+1) = 1 := by rw [pow_succ, hodd]; norm_num
    rw [hodd, heven]
    ring

theorem integral_hillRiccatiQuadratic_even (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) (m : ℕ) :
    (∫ x in (0 : ℝ)..1, evaluate q 0 (hillRiccatiQuadratic (2*m+2)) x) =
      (-1 : ℂ)^(m+1) * ∫ x in (0 : ℝ)..1, (iteratedDeriv m q x)^2 := by
  rw [integral_hillRiccatiQuadratic_recurrence q hq hp]
  have hterm (ij : ℕ × ℕ) (hij : ij ∈ Finset.antidiagonal (2*m)) :
      (∫ x in (0 : ℝ)..1, evaluate q 0 (hillRiccatiLinear ij.1*hillRiccatiLinear ij.2) x) =
        (-1 : ℂ)^(ij.1+m) * ∫ x in (0 : ℝ)..1, (iteratedDeriv m q x)^2 := by
    have he := Finset.mem_antidiagonal.mp hij
    have hpow : (-1 : ℂ)^ij.1 * (-1 : ℂ)^ij.2 = 1 := by
      rw [← pow_add, he, pow_mul, neg_one_sq, one_pow]
    have hf : evaluate q 0 (hillRiccatiLinear ij.1*hillRiccatiLinear ij.2) =
        fun x => iteratedDeriv ij.1 q x * iteratedDeriv ij.2 q x := by
      funext x
      simp only [evaluate_mul, hillRiccatiLinear, evaluate_C, evaluate_X,
        Bool.false_eq_true, ↓reduceIte, Pi.mul_apply]
      calc
        _ = ((-1 : ℂ)^ij.1 * (-1 : ℂ)^ij.2) *
            (iteratedDeriv ij.1 q x * iteratedDeriv ij.2 q x) := by ring
        _ = _ := by rw [hpow, one_mul]
    rw [hf]
    exact integral_scalar_jet_product q hq hp ij.1 ij.2 m he
  rw [Finset.sum_congr rfl hterm]
  simp_rw [pow_add]
  rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Nat.succ_eq_add_one]
  rw [sum_neg_one_even_range]
  rw [pow_succ]
  ring

theorem integral_hillRiccatiLinear_succ (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) (n : ℕ) :
    (∫ x in (0 : ℝ)..1, evaluate q 0 (hillRiccatiLinear (n+1)) x) = 0 := by
  have hi := integral_evaluate_spatialDerivative q 0 hq contDiff_const hp (fun _ => rfl)
    (hillRiccatiLinear n)
  rw [spatialDerivative_hillRiccatiLinear] at hi
  simpa only [evaluate_neg, Pi.neg_apply, intervalIntegral.integral_neg, neg_eq_zero] using hi

/-- Source Lemma 7, with the exact scalar grading and half kinetic normalization. -/
theorem exists_classicalKdVHierarchyHamiltonian_reduced_polynomial (m : ℕ) (hm : 1 ≤ m) :
    ∃ p : DifferentialPolynomial.Polynomial, JetOrderLE p (m-1) ∧
      p.IsWeightedHomogeneous hillJetWeight (2*(m : ℤ)+4) ∧
      ∀ q : ℝ → ℂ, ContDiff ℝ ∞ q → Function.Periodic q 1 →
        classicalKdVHierarchyHamiltonian q m = (1/2 : ℂ) * ∫ x in (0 : ℝ)..1,
          (iteratedDeriv m q x)^2 + evaluate q 0 p x := by
  obtain ⟨p,r,he,hp,hw,_⟩ := exists_hillRiccatiCubicRemainder_reduction m hm
  let sign : ℂ := (-1)^(m+1)
  have hc : JetOrderLE (C sign) (m-1) := Supported.monomial 0 sign (by simp)
  refine ⟨C sign*p,hc.mul hp,hw.C_mul sign,?_⟩
  intro q hq hperiod
  have hR := integral_evaluate_eq_of_total_derivative q 0 hq contDiff_const hperiod
    (fun _ => rfl) _ p r he
  have hpoly : hillRiccatiPolynomial (2*m+2) =
      hillRiccatiLinear (2*m+2)+hillRiccatiQuadratic (2*m+2)+hillRiccatiCubicRemainder (2*m+2) := by
    simp only [hillRiccatiCubicRemainder, hillRiccatiNonlinear]
    ring
  have h1 : IntervalIntegrable
      (fun x => evaluate q 0 (hillRiccatiLinear (2*m+2)) x) volume 0 1 :=
    (continuous_evaluate q 0 hq contDiff_const _).intervalIntegrable 0 1
  have h2 : IntervalIntegrable
      (fun x => evaluate q 0 (hillRiccatiQuadratic (2*m+2)) x) volume 0 1 :=
    (continuous_evaluate q 0 hq contDiff_const _).intervalIntegrable 0 1
  have h3 : IntervalIntegrable
      (fun x => evaluate q 0 (hillRiccatiCubicRemainder (2*m+2)) x) volume 0 1 :=
    (continuous_evaluate q 0 hq contDiff_const _).intervalIntegrable 0 1
  have hsum : (∫ x in (0 : ℝ)..1, evaluate q 0 (hillRiccatiPolynomial (2*m+2)) x) =
      (∫ x in (0 : ℝ)..1, evaluate q 0 (hillRiccatiLinear (2*m+2)) x) +
      (∫ x in (0 : ℝ)..1, evaluate q 0 (hillRiccatiQuadratic (2*m+2)) x) +
      (∫ x in (0 : ℝ)..1, evaluate q 0 (hillRiccatiCubicRemainder (2*m+2)) x) := by
    rw [hpoly]
    simp only [evaluate_add, Pi.add_apply]
    rw [intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2]
  have hL := integral_hillRiccatiLinear_succ q hq hperiod (2*m+1)
  have hQ := integral_hillRiccatiQuadratic_even q hq hperiod m
  have hkin : IntervalIntegrable (fun x => (iteratedDeriv m q x)^2) volume 0 1 :=
    ((hq.continuous_iteratedDeriv m (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)).pow 2).intervalIntegrable 0 1
  have hP : IntervalIntegrable (fun x => evaluate q 0 (C sign*p) x) volume 0 1 :=
    (continuous_evaluate q 0 hq contDiff_const _).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hkin hP]
  simp only [evaluate_mul, evaluate_C, Pi.mul_apply, intervalIntegral.integral_const_mul]
  rw [classicalKdVHierarchyHamiltonian, hsum, hL, zero_add, hQ, hR]
  have hsign : sign*sign = 1 := by
    dsimp only [sign]
    rw [← mul_pow]
    norm_num
  change sign/2*(sign*_+_) = _
  linear_combination hsign * (∫ x in (0 : ℝ)..1, (iteratedDeriv m q x)^2) / 2

end NLS.KdV
