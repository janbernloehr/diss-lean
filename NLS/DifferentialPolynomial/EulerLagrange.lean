import NLS.DifferentialPolynomial.PeriodicEvaluation
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Euler derivatives of arbitrary differential polynomials

The finite sum uses precisely the jets occurring in the input. Repeated
periodic integration by parts transfers every derivative from a variation to
its coefficient, with no order bound on the polynomial.
-/
noncomputable section
open MvPolynomial Set MeasureTheory
open scoped ContDiff
namespace NLS.DifferentialPolynomial

/-- Formal Euler derivative with respect to either of the two scalar fields. -/
def eulerDerivative (field : Bool) (p : Polynomial) : Polynomial :=
  ∑ v ∈ p.vars, if v.1 = field then
    C ((-1 : ℂ)^v.2) * ((spatialDerivative : Polynomial → Polynomial)^[v.2]) (pderiv v p)
    else 0

/-- The pointwise first variation before integration by parts. -/
def firstVariationDensity (a b h k : ℝ → ℂ) (p : Polynomial) (x : ℝ) : ℂ :=
  ∑ v ∈ p.vars, iteratedDeriv v.2 (if v.1 then k else h) x *
    evaluate a b (pderiv v p) x

theorem contDiff_evaluate (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (p : Polynomial) : ContDiff ℝ ∞ (evaluate a b p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [evaluate_C] using contDiff_const (c := c)
  | add p q hp hq => simpa only [evaluate_add, Pi.add_def] using hp.add hq
  | mul_X p v hp =>
    rw [evaluate_mul, evaluate_X]
    exact hp.mul (NLS.FunctionalAnalysis.contDiff_iteratedDeriv _ (by split <;> assumption) v.2)

theorem evaluate_iterate_spatialDerivative (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (p : Polynomial) (n : ℕ) :
    evaluate a b (((spatialDerivative : Polynomial → Polynomial)^[n]) p) =
      iteratedDeriv n (evaluate a b p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', evaluate_spatialDerivative a b ha hb, ih,
      iteratedDeriv_succ]

theorem evaluate_eulerDerivative (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (field : Bool) (p : Polynomial) (x : ℝ) :
    evaluate a b (eulerDerivative field p) x =
      ∑ v ∈ p.vars, if v.1 = field then
        (-1 : ℂ)^v.2 * iteratedDeriv v.2 (evaluate a b (pderiv v p)) x else 0 := by
  classical
  simp only [eulerDerivative, evaluate, map_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp only [map_mul, eval_C, map_zero]
  rw [← evaluate, evaluate_iterate_spatialDerivative a b ha hb]

/-- The physical periodic integral of the first variation is the bilinear
pairing with the two Euler derivatives. -/
theorem integral_firstVariationDensity (a b h k : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hh : ContDiff ℝ ∞ h) (hk : ContDiff ℝ ∞ k)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) (hpk : Function.Periodic k 1) (p : Polynomial) :
    (∫ x in (0 : ℝ)..1, firstVariationDensity a b h k p x) =
      ∫ x in (0 : ℝ)..1, h x * evaluate a b (eulerDerivative false p) x +
        k x * evaluate a b (eulerDerivative true p) x := by
  classical
  have hc (v : Jet) : Continuous (fun x =>
      iteratedDeriv v.2 (if v.1 then k else h) x * evaluate a b (pderiv v p) x) :=
    (NLS.FunctionalAnalysis.contDiff_iteratedDeriv _ (by split <;> assumption) v.2).continuous.mul
      (continuous_evaluate a b ha hb _)
  have hd (v : Jet) : Continuous (fun x =>
      (if v.1 then k else h) x *
        ((-1 : ℂ)^v.2 * iteratedDeriv v.2 (evaluate a b (pderiv v p)) x)) :=
    (show Continuous (if v.1 then k else h) from by split <;> first | exact hk.continuous | exact hh.continuous).mul
      (continuous_const.mul (NLS.FunctionalAnalysis.contDiff_iteratedDeriv _
        (contDiff_evaluate a b ha hb _) v.2).continuous)
  have he (x : ℝ) :
      h x * evaluate a b (eulerDerivative false p) x +
        k x * evaluate a b (eulerDerivative true p) x =
      ∑ v ∈ p.vars, (if v.1 then k else h) x *
        ((-1 : ℂ)^v.2 * iteratedDeriv v.2 (evaluate a b (pderiv v p)) x) := by
    rw [evaluate_eulerDerivative a b ha hb, evaluate_eulerDerivative a b ha hb,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    cases v.1 <;> simp
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun v _ => (hd v).intervalIntegrable 0 1)]
  unfold firstVariationDensity
  rw [intervalIntegral.integral_finsetSum (fun v _ => (hc v).intervalIntegrable 0 1)]
  apply Finset.sum_congr rfl
  intro v _
  rw [NLS.FunctionalAnalysis.integral_iteratedDeriv_mul_periodic _ _
    (by split <;> assumption) (contDiff_evaluate a b ha hb _)
    (by split <;> assumption) (periodic_evaluate a b 1 hpa hpb _)]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  ring

end NLS.DifferentialPolynomial
