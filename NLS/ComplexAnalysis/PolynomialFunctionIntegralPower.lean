import NLS.ComplexAnalysis.PolynomialFunctionBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Integral bounds preserving a polynomial zero

Integrated coefficient bounds control a polynomial of functions while retaining its exact vanishing order in the inverse-frequency parameter.
-/

noncomputable section
open Set Complex MeasureTheory
namespace NLS.ComplexAnalysis

/-- Integrated coefficient bounds retain an exact zero's power in the
inverse-frequency parameter, without pointwise bounds on those coefficients. -/
theorem integral_polynomial_function_power_le
    (Q : Polynomial (ℝ → ℂ)) (hQ : ∀ k : ℕ, Continuous (Q.coeff k))
    (N D : ℕ) (hD : Q.natDegree < D) (hdiv : Polynomial.X^N ∣ Q)
    (C : ℕ → ℝ) (hC : ∀ k ∈ Finset.range D, (∫ x in (0:ℝ)..1, ‖Q.coeff k x‖) ≤ C k)
    (w : ℂ) (hw : ‖w‖ ≤ 1) :
    (∫ x in (0:ℝ)..1, ‖Q.eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w‖) ≤
      (∑ k ∈ Finset.range D, C k)*‖w‖^N := by
  have hpoint (x : ℝ) :
      ‖Q.eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w‖ ≤
        ∑ k ∈ Finset.range D, ‖Q.coeff k x‖*‖w‖^N := by
    rw [Polynomial.eval₂_eq_sum_range' _ hD]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    change ‖Q.coeff k x*w^k‖ ≤ _
    by_cases hk : k < N
    · rw [(Polynomial.X_pow_dvd_iff.mp hdiv) k hk]
      simp
    · rw [norm_mul,norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (norm_nonneg w) hw (by omega)) (norm_nonneg _)
  have hi (k : ℕ) : IntervalIntegrable (fun x => ‖Q.coeff k x‖*‖w‖^N) volume 0 1 :=
    ((hQ k).norm.mul continuous_const).intervalIntegrable 0 1
  have heval : Continuous (fun x : ℝ => Q.eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w) :=
    (continuous_polynomial_function_eval Q hQ).comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => w)))
  have hsum : Continuous (fun x : ℝ => ∑ k ∈ Finset.range D, ‖Q.coeff k x‖*‖w‖^N) :=
    continuous_finsetSum _ (fun k _ => (hQ k).norm.mul continuous_const)
  calc
    _ ≤ ∫ x in (0:ℝ)..1, ∑ k ∈ Finset.range D, ‖Q.coeff k x‖*‖w‖^N := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (heval.norm.intervalIntegrable 0 1) (hsum.intervalIntegrable 0 1) (fun x _ => hpoint x)
    _ = ∑ k ∈ Finset.range D, (∫ x in (0:ℝ)..1, ‖Q.coeff k x‖)*‖w‖^N := by
      rw [intervalIntegral.integral_finsetSum (fun k _ => hi k)]
      apply Finset.sum_congr rfl
      intro k _
      exact intervalIntegral.integral_mul_const _ _
    _ ≤ ∑ k ∈ Finset.range D, C k*‖w‖^N := Finset.sum_le_sum
      (fun k hk => mul_le_mul_of_nonneg_right (hC k hk) (by positivity))
    _ = _ := (Finset.sum_mul _ _ _).symm

end NLS.ComplexAnalysis
